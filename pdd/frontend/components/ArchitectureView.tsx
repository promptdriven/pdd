import React, { useState, useEffect, useCallback, useRef, useMemo } from 'react';
import { api, ArchitectureModule, PromptInfo, PromptGenerationResult, ArchitectureValidationResult, ArchitectureSyncResult, GenerationGlobalOptions } from '../api';
import DependencyViewer from './DependencyViewer';
import FileBrowser from './FileBrowser';
import GenerationProgressModal from './GenerationProgressModal';
import PromptOrderModal from './PromptOrderModal';
import GraphToolbar from './GraphToolbar';
import ModuleEditModal from './ModuleEditModal';
import AddModuleModal from './AddModuleModal';
import GroupEditModal from './GroupEditModal';
import SyncFromPromptModal from './SyncFromPromptModal';
import SyncOptionsModal from './SyncOptionsModal';
import { useArchitectureHistory } from '../hooks/useArchitectureHistory';
import { COMMANDS } from '../constants';
import { CommandType } from '../types';
import { buildDisplayCommand } from '../lib/commandBuilder';
import BatchFilterDropdown from './BatchFilterDropdown';
import { computeBatches, filterModulesByBatch } from '../lib/batchUtils';
import type { Batch } from '../lib/batchUtils';

interface ArchitectureViewProps {
  serverConnected: boolean;
  isExecuting: boolean;
  onOpenPromptSpace: (prompt: PromptInfo) => void;
  // Batch operation callbacks for job dashboard tracking
  onBatchStart?: (name: string, total: number) => void;
  onBatchProgress?: (current: number, total: number, currentItem: string) => void;
  onBatchComplete?: (success: boolean) => void;
  // Remote execution support
  executionMode: 'local' | 'remote';
  selectedRemoteSession: string | null;
  // Callback to add remote jobs to job dashboard
  onRemoteJobSubmitted?: (displayCommand: string, commandType: string, commandId: string, sessionId: string) => void;
  // Callback to add tasks to the job queue
  onAddToQueue?: (commandType: CommandType, prompt: PromptInfo, rawOptions: Record<string, any>, displayCommand: string) => void;
  // Callback to run sync directly (not queued)
  onRunSync?: (prompt: PromptInfo, options?: Record<string, any>) => void;
  // Counter that increments when a sync task/job completes, triggering a prompt refresh
  syncCompletedCounter?: number;
}

type EditorMode = 'empty' | 'editor' | 'graph';

/**
 * Determine if a module still needs syncing based on its expected outputs.
 * Config-type languages (JSON, YAML, CSS) only expect "code", while
 * executable languages expect "code", "test", and "example".
 */
export function moduleNeedsSync(info: PromptInfo | undefined): boolean {
  if (!info) return true;
  const expected = info.expected_outputs ?? ['code', 'test', 'example'];
  return expected.some(output => !info[output as keyof PromptInfo]);
}

const ArchitectureView: React.FC<ArchitectureViewProps> = ({
  serverConnected,
  isExecuting,
  onOpenPromptSpace,
  onBatchStart,
  onBatchProgress,
  onBatchComplete,
  executionMode,
  selectedRemoteSession,
  onRemoteJobSubmitted,
  onAddToQueue,
  onRunSync,
  syncCompletedCounter,
}) => {
  // Architecture state
  const [architecture, setArchitecture] = useState<ArchitectureModule[] | null>(null);
  const [loading, setLoading] = useState(true);
  const [error, setError] = useState<string | null>(null);

  // Editor state
  const [mode, setMode] = useState<EditorMode>('empty');
  const [appName, setAppName] = useState('');
  const [prdContent, setPrdContent] = useState('');
  const [showFileBrowser, setShowFileBrowser] = useState<'architecture' | null>(null);
  const [architecturePathInput, setArchitecturePathInput] = useState('architecture.json');
  const [loadArchitectureError, setLoadArchitectureError] = useState<string | null>(null);

  // GitHub issue URL generation state
  const [issueUrl, setIssueUrl] = useState('');
  const [isGeneratingFromIssue, setIsGeneratingFromIssue] = useState(false);
  const [issueGenerationError, setIssueGenerationError] = useState<string | null>(null);

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
  const [globalOptions, setGlobalOptions] = useState<GenerationGlobalOptions>({});

  // Cancel ref for batch generation
  const cancelRequestedRef = useRef(false);

  // Sidebar collapsed state
  const [sidebarCollapsed, setSidebarCollapsed] = useState(false);

  // Existing prompts state - track which prompts already exist with their file info
  const [existingPrompts, setExistingPrompts] = useState<Set<string>>(new Set());
  const [promptsInfo, setPromptsInfo] = useState<PromptInfo[]>([]);

  // Edit mode state
  const [editMode, setEditMode] = useState(false);
  const [showEditModal, setShowEditModal] = useState(false);
  const [showAddModal, setShowAddModal] = useState(false);
  const [selectedModule, setSelectedModule] = useState<ArchitectureModule | null>(null);

  // Group management state
  const [expandedGroups, setExpandedGroups] = useState<Set<string>>(new Set());
  const [showGroupModal, setShowGroupModal] = useState(false);
  const [editingGroupName, setEditingGroupName] = useState<string | null>(null);
  const [isSaving, setIsSaving] = useState(false);
  const [isRearranging, setIsRearranging] = useState(false);
  const [rearrangeVersion, setRearrangeVersion] = useState(0);
  const [validationResult, setValidationResult] = useState<ArchitectureValidationResult | null>(null);
  const [highlightedModules, setHighlightedModules] = useState<Set<string>>(new Set());

  // Mobile detection state
  const [isMobile, setIsMobile] = useState(window.innerWidth < 768);

  // Sync from prompts state
  const [showSyncModal, setShowSyncModal] = useState(false);
  const [isSyncing, setIsSyncing] = useState(false);
  const [syncResult, setSyncResult] = useState<ArchitectureSyncResult | null>(null);

  // Sync options modal state (for configuring sync options before running pdd sync)
  const [showSyncOptionsModal, setShowSyncOptionsModal] = useState(false);
  const [pendingSyncModule, setPendingSyncModule] = useState<ArchitectureModule | null>(null);
  const [pendingSyncAll, setPendingSyncAll] = useState(false);

  // Batch (connected component) filtering state
  const [selectedBatch, setSelectedBatch] = useState<Batch | null>(null);
  const [pendingSyncBatch, setPendingSyncBatch] = useState<Batch | null>(null);

  // Architecture history hook for undo/redo
  const {
    architecture: editableArchitecture,
    hasUnsavedChanges,
    addModule,
    updateModule,
    batchUpdateModules,
    deleteModule,
    addDependency,
    removeDependency,
    updatePositions,
    undo,
    redo,
    canUndo,
    canRedo,
    setOriginal,
    discardChanges,
  } = useArchitectureHistory([]);

  // Sync architecture with history hook
  useEffect(() => {
    if (architecture) {
      setOriginal(architecture);
    }
  }, [architecture, setOriginal]);

  // Auto-expand any newly-appearing groups when architecture changes
  useEffect(() => {
    if (architecture) {
      const groupNames = architecture.filter(m => m.group).map(m => m.group!);
      if (groupNames.length > 0) {
        setExpandedGroups(prev => {
          const next = new Set(prev);
          groupNames.forEach(g => { if (!next.has(g)) next.add(g); });
          return next;
        });
      }
    }
  }, [architecture]);

  // Mobile detection useEffect
  useEffect(() => {
    const handleResize = () => setIsMobile(window.innerWidth < 768);
    window.addEventListener('resize', handleResize);
    return () => window.removeEventListener('resize', handleResize);
  }, []);

  // Display architecture: use editable version if in edit mode
  const displayArchitecture = editMode ? editableArchitecture : architecture;

  // Compute batches (connected components) from architecture
  const batches = useMemo(() => {
    if (!displayArchitecture) return [];
    return computeBatches(displayArchitecture);
  }, [displayArchitecture]);

  // Filter architecture by selected batch for display
  const filteredArchitecture = useMemo(() => {
    if (!displayArchitecture) return null;
    return filterModulesByBatch(displayArchitecture, selectedBatch);
  }, [displayArchitecture, selectedBatch]);

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

  // Refresh prompts when a sync task/job completes (counter increments)
  useEffect(() => {
    if (syncCompletedCounter && syncCompletedCounter > 0) {
      loadExistingPrompts();
    }
  }, [syncCompletedCounter, loadExistingPrompts]);

  // Handle file selection from browser (architecture files only)
  const handleFileSelect = useCallback(async (path: string) => {
    try {
      const content = await api.getFileContent(path);
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
      setShowFileBrowser(null);
    } catch (e: any) {
      console.error('Failed to load file:', e);
    }
  }, [loadExistingPrompts]);

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

  // Generate architecture from GitHub issue URL
  const handleGenerateFromIssue = async () => {
    if (!issueUrl.trim()) {
      setIssueGenerationError('Please enter a GitHub issue URL');
      return;
    }

    // Validate URL format
    const githubIssuePattern = /github\.com\/[^/]+\/[^/]+\/issues\/\d+/;
    if (!githubIssuePattern.test(issueUrl)) {
      setIssueGenerationError('Invalid GitHub issue URL format. Expected: https://github.com/owner/repo/issues/123');
      return;
    }

    setIsGeneratingFromIssue(true);
    setIssueGenerationError(null);

    try {
      // Check if we're in remote mode
      if (executionMode === 'remote' && selectedRemoteSession) {
        // Submit to remote session - pass issue URL as prompt_file argument
        try {
          await api.submitRemoteCommand({
            sessionId: selectedRemoteSession,
            type: 'generate',
            payload: { args: { prompt_file: issueUrl }, options: {} },
          });

          // Clear the input and notify user
          setIssueUrl('');
          setIssueGenerationError(null);

          // Notify via callback if available
          if (onRemoteJobSubmitted) {
            const displayCommand = `pdd generate ${issueUrl}`;
            onRemoteJobSubmitted(displayCommand, 'generate', `issue-${Date.now()}`, selectedRemoteSession);
          }

          alert('Architecture generation from GitHub issue submitted to remote session. Check the remote machine for results.');
        } catch (error) {
          setIssueGenerationError(`Failed to submit remote command: ${error instanceof Error ? error.message : String(error)}`);
        }
      } else {
        // Local execution
        const result = await api.generateArchitectureFromIssue(issueUrl, {});

        if (result.success) {
          // Job started - show message to user
          alert(`Architecture generation started. A terminal window will open to run the agentic workflow.\n\nJob ID: ${result.job_id}`);

          // Clear the input
          setIssueUrl('');
        } else {
          setIssueGenerationError(result.message || 'Failed to start architecture generation');
        }
      }
    } catch (e: any) {
      console.error('Failed to generate architecture from issue:', e);
      setIssueGenerationError(e.message || 'Failed to start architecture generation');
    } finally {
      setIsGeneratingFromIssue(false);
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

  // Open the order modal before generating prompts
  const handleGeneratePrompts = useCallback(() => {
    if (!architecture || architecture.length === 0) return;
    setShowOrderModal(true);
  }, [architecture]);

  // Compute how many modules still need syncing (missing code, test, or example)
  const remainingModulesCount = useMemo(() => {
    if (!architecture) return 0;
    const promptMap = new Map<string, PromptInfo>();
    promptsInfo.forEach(p => {
      const filename = p.prompt.split('/').pop() || '';
      promptMap.set(filename, p);
    });
    return architecture.filter(module => {
      const info = promptMap.get(module.filename);
      return moduleNeedsSync(info);
    }).length;
  }, [architecture, promptsInfo]);

  // Compute remaining modules per batch
  const remainingCountByBatch = useMemo(() => {
    const counts = new Map<number, number>();
    if (!batches.length) return counts;

    const promptMap = new Map<string, PromptInfo>();
    promptsInfo.forEach(p => {
      const filename = p.prompt.split('/').pop() || '';
      promptMap.set(filename, p);
    });

    for (const batch of batches) {
      const remaining = batch.modules.filter(module => {
        const info = promptMap.get(module.filename);
        return moduleNeedsSync(info);
      }).length;
      counts.set(batch.id, remaining);
    }
    return counts;
  }, [batches, promptsInfo]);

  // Helper: build a PromptInfo from an architecture module
  const buildPromptInfoForModule = useCallback((module: ArchitectureModule): PromptInfo => {
    const promptMap = new Map<string, PromptInfo>();
    promptsInfo.forEach(p => {
      const filename = p.prompt.split('/').pop() || '';
      promptMap.set(filename, p);
    });

    const match = module.filename.match(/_([A-Za-z]+)\.prompt$/);
    const language = match ? match[1].toLowerCase() : undefined;
    const basename = module.filename.replace(/_[A-Za-z]+\.prompt$/, '');

    const existingPrompt = promptMap.get(module.filename);
    return existingPrompt || {
      prompt: `prompts/${module.filename}`,
      sync_basename: basename,
      language,
      code: module.filepath,
    };
  }, [promptsInfo]);

  // Helper: get modules that still need syncing from a list
  const getModulesNeedingSync = useCallback((modules: ArchitectureModule[]): ArchitectureModule[] => {
    const promptMap = new Map<string, PromptInfo>();
    promptsInfo.forEach(p => {
      const filename = p.prompt.split('/').pop() || '';
      promptMap.set(filename, p);
    });

    return modules
      .filter(module => {
        const info = promptMap.get(module.filename);
        return moduleNeedsSync(info);
      })
      .sort((a, b) => a.priority - b.priority);
  }, [promptsInfo]);

  // Show sync options modal for a single module
  const handleRunSyncForModule = useCallback((module: ArchitectureModule) => {
    if (!onAddToQueue && !onRunSync) return;
    setPendingSyncModule(module);
    setPendingSyncAll(false);
    setShowSyncOptionsModal(true);
  }, [onAddToQueue, onRunSync]);

  // Show sync options modal for all remaining modules
  const handleSyncAll = useCallback(() => {
    if (!architecture || (!onAddToQueue && !onRunSync)) return;
    setPendingSyncModule(null);
    setPendingSyncAll(true);
    setPendingSyncBatch(null);
    setShowSyncOptionsModal(true);
  }, [architecture, onAddToQueue, onRunSync]);

  // Show sync options modal for a specific batch
  const handleSyncBatch = useCallback((batch: Batch) => {
    if (!onAddToQueue && !onRunSync) return;
    setPendingSyncModule(null);
    setPendingSyncAll(false);
    setPendingSyncBatch(batch);
    setShowSyncOptionsModal(true);
  }, [onAddToQueue, onRunSync]);

  // Run sync directly for a single module
  const runSyncForModule = useCallback((module: ArchitectureModule, options: Record<string, any>) => {
    if (!onRunSync) return;
    const promptInfo = buildPromptInfoForModule(module);
    onRunSync(promptInfo, options);
  }, [buildPromptInfoForModule, onRunSync]);

  // Run sync directly for all remaining modules (runs only the first; rest queued)
  const runSyncAll = useCallback((options: Record<string, any>) => {
    if (!architecture || !onRunSync) return;
    const modulesToSync = getModulesNeedingSync(architecture);
    if (modulesToSync.length === 0) return;

    // Run the first module directly
    runSyncForModule(modulesToSync[0], options);

    // Queue the rest if onAddToQueue is available
    if (onAddToQueue && modulesToSync.length > 1) {
      modulesToSync.slice(1).forEach(module => {
        const promptInfo = buildPromptInfoForModule(module);
        const displayCommand = buildDisplayCommand(CommandType.SYNC, promptInfo, { ...options });
        onAddToQueue(CommandType.SYNC, promptInfo, { ...options }, displayCommand);
      });
    }
  }, [architecture, getModulesNeedingSync, runSyncForModule, buildPromptInfoForModule, onRunSync, onAddToQueue]);

  // Run sync directly for a specific batch (runs first; rest queued)
  const runSyncBatch = useCallback((batch: Batch, options: Record<string, any>) => {
    if (!onRunSync) return;
    const modulesToSync = getModulesNeedingSync(batch.modules);
    if (modulesToSync.length === 0) return;

    runSyncForModule(modulesToSync[0], options);

    if (onAddToQueue && modulesToSync.length > 1) {
      modulesToSync.slice(1).forEach(module => {
        const promptInfo = buildPromptInfoForModule(module);
        const displayCommand = buildDisplayCommand(CommandType.SYNC, promptInfo, { ...options });
        onAddToQueue(CommandType.SYNC, promptInfo, { ...options }, displayCommand);
      });
    }
  }, [getModulesNeedingSync, runSyncForModule, buildPromptInfoForModule, onRunSync, onAddToQueue]);

  // Queue sync for a single module
  const queueSyncForModule = useCallback((module: ArchitectureModule, options: Record<string, any>) => {
    if (!onAddToQueue) return;
    const promptInfo = buildPromptInfoForModule(module);
    const displayCommand = buildDisplayCommand(CommandType.SYNC, promptInfo, { ...options });
    onAddToQueue(CommandType.SYNC, promptInfo, { ...options }, displayCommand);
  }, [buildPromptInfoForModule, onAddToQueue]);

  // Queue sync for all remaining modules
  const queueSyncAll = useCallback((options: Record<string, any>) => {
    if (!architecture || !onAddToQueue) return;
    const modulesToSync = getModulesNeedingSync(architecture);
    if (modulesToSync.length === 0) return;

    modulesToSync.forEach(module => {
      const promptInfo = buildPromptInfoForModule(module);
      const displayCommand = buildDisplayCommand(CommandType.SYNC, promptInfo, { ...options });
      onAddToQueue(CommandType.SYNC, promptInfo, { ...options }, displayCommand);
    });
  }, [architecture, getModulesNeedingSync, buildPromptInfoForModule, onAddToQueue]);

  // Queue sync for a specific batch
  const queueSyncBatch = useCallback((batch: Batch, options: Record<string, any>) => {
    if (!onAddToQueue) return;
    const modulesToSync = getModulesNeedingSync(batch.modules);
    if (modulesToSync.length === 0) return;

    modulesToSync.forEach(module => {
      const promptInfo = buildPromptInfoForModule(module);
      const displayCommand = buildDisplayCommand(CommandType.SYNC, promptInfo, { ...options });
      onAddToQueue(CommandType.SYNC, promptInfo, { ...options }, displayCommand);
    });
  }, [getModulesNeedingSync, buildPromptInfoForModule, onAddToQueue]);

  // Handle sync options modal "Run Sync" button
  const handleSyncOptionsConfirm = useCallback((options: Record<string, any>) => {
    if (pendingSyncAll) {
      onRunSync ? runSyncAll(options) : queueSyncAll(options);
    } else if (pendingSyncBatch) {
      onRunSync ? runSyncBatch(pendingSyncBatch, options) : queueSyncBatch(pendingSyncBatch, options);
    } else if (pendingSyncModule) {
      onRunSync ? runSyncForModule(pendingSyncModule, options) : queueSyncForModule(pendingSyncModule, options);
    }
    setShowSyncOptionsModal(false);
    setPendingSyncModule(null);
    setPendingSyncAll(false);
    setPendingSyncBatch(null);
  }, [pendingSyncAll, pendingSyncBatch, pendingSyncModule, onRunSync, runSyncAll, runSyncBatch, runSyncForModule, queueSyncAll, queueSyncBatch, queueSyncForModule]);

  // Handle sync options modal "Add to Queue" button
  const handleSyncOptionsAddToQueue = useCallback((options: Record<string, any>) => {
    if (pendingSyncAll) {
      queueSyncAll(options);
    } else if (pendingSyncBatch) {
      queueSyncBatch(pendingSyncBatch, options);
    } else if (pendingSyncModule) {
      queueSyncForModule(pendingSyncModule, options);
    }
    setShowSyncOptionsModal(false);
    setPendingSyncModule(null);
    setPendingSyncAll(false);
    setPendingSyncBatch(null);
  }, [pendingSyncAll, pendingSyncBatch, pendingSyncModule, queueSyncAll, queueSyncBatch, queueSyncForModule]);

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
    onBatchStart?.('Generating Prompts', moduleRequests.length + 1); // +1 for .pddrc generation

    try {
      // Step 1: Generate .pddrc from architecture.json before generating prompts
      setPromptGenerationProgress({ current: 0, total: moduleRequests.length, currentModule: '.pddrc' });

      if (executionMode === 'remote' && selectedRemoteSession) {
        // Remote: submit .pddrc generation command first
        try {
          const pddrcOptions: Record<string, any> = {
            template: 'generic/generate_pddrc',
            env: ['ARCHITECTURE_FILE=architecture.json'],
            output: '.pddrc',
          };
          if (globalOptions?.force) pddrcOptions.force = true;

          const { commandId } = await api.submitRemoteCommand({
            sessionId: selectedRemoteSession,
            type: 'generate',
            payload: { args: {}, options: pddrcOptions },
          });

          onRemoteJobSubmitted?.(
            '[Remote] pdd generate --template generic/generate_pddrc -o .pddrc',
            'generate',
            commandId,
            selectedRemoteSession
          );
        } catch (e) {
          console.warn('Failed to submit .pddrc generation to remote:', e);
        }
      } else {
        // Local: generate .pddrc and wait for completion
        try {
          await api.generatePddrcFromArchitecture({
            architectureFile: 'architecture.json',
            globalOptions,
          });
        } catch (e) {
          console.warn('Failed to generate .pddrc:', e);
        }
      }

      // Step 2: Generate prompts
      // Check if we're in remote mode
      if (executionMode === 'remote' && selectedRemoteSession) {
        // Remote execution: submit each prompt generation command to remote session
        const results: PromptGenerationResult[] = [];

        for (let i = 0; i < moduleRequests.length; i++) {
          if (cancelRequestedRef.current) break;

          const { module, langOrFramework } = moduleRequests[i];
          setPromptGenerationProgress({ current: i + 1, total: moduleRequests.length, currentModule: module });
          onBatchProgress?.(i + 1, moduleRequests.length, module);

          try {
            // Build the options structure for generatePromptFromArchitecture
            const envArgs: string[] = [
              `MODULE=${module}`,
              `LANG_OR_FRAMEWORK=${langOrFramework}`,
              `ARCHITECTURE_FILE=architecture.json`,
            ];

            const options: Record<string, any> = {
              template: 'generic/generate_prompt',
              env: envArgs,
              output: `prompts/${module}_${langOrFramework}.prompt`,
            };

            // Submit to remote session
            const { commandId } = await api.submitRemoteCommand({
              sessionId: selectedRemoteSession,
              type: 'generate',
              payload: { args: {}, options },
            });

            // Add to job dashboard for tracking
            const displayCommand = `pdd generate --template generic/generate_prompt -o prompts/${module}_${langOrFramework}.prompt`;
            onRemoteJobSubmitted?.(
              `[Remote] ${displayCommand}`,
              'generate',
              commandId,
              selectedRemoteSession
            );

            results.push({
              module: `${module}_${langOrFramework}`,
              success: true, // Submission succeeded - actual completion tracked in job dashboard
            });
          } catch (e) {
            results.push({
              module: `${module}_${langOrFramework}`,
              success: false,
              error: e instanceof Error ? e.message : String(e),
            });
          }
        }

        setPromptGenerationResults(results);
        // For remote mode, "success" means successfully submitted, not completed
        const allSubmitted = results.every(r => r.success);
        onBatchComplete?.(allSubmitted);
      } else {
        // Local execution: use existing batch generation
        const results = await api.batchGeneratePrompts(
          {
            modules: moduleRequests,
            architectureFile: 'architecture.json',
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
      }
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
  }, [onBatchStart, onBatchProgress, onBatchComplete, executionMode, selectedRemoteSession, onRemoteJobSubmitted]);

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

  // ==================== Sync from Prompts Handlers ====================

  // Open sync modal
  const handleOpenSyncModal = useCallback(() => {
    setSyncResult(null);
    setShowSyncModal(true);
  }, []);

  // Perform sync from prompts
  const handleSync = useCallback(async () => {
    setIsSyncing(true);
    try {
      const result = await api.syncArchitectureFromPrompts({ dry_run: false });
      setSyncResult(result);

      // If sync succeeded and validation passed, reload architecture
      if (result.success && result.validation.valid) {
        const modules = await api.getArchitecture();
        setArchitecture(modules);
        // Refresh existing prompts
        await loadExistingPrompts();
      }
    } catch (e: any) {
      console.error('Sync failed:', e);
      setSyncResult({
        success: false,
        updated_count: 0,
        skipped_count: 0,
        results: [],
        validation: { valid: true, errors: [], warnings: [] },
        errors: [e.message || 'Unexpected error during sync'],
      });
    } finally {
      setIsSyncing(false);
    }
  }, [loadExistingPrompts]);

  // Close sync modal
  const handleCloseSyncModal = useCallback(() => {
    setShowSyncModal(false);
    setSyncResult(null);
  }, []);

  // ==================== Edit Mode Handlers ====================

  // Toggle edit mode
  const handleToggleEditMode = useCallback(() => {
    if (editMode && hasUnsavedChanges) {
      // Ask user to save or discard changes
      const shouldDiscard = window.confirm('You have unsaved changes. Discard them?');
      if (shouldDiscard) {
        discardChanges();
        setValidationResult(null);
        setHighlightedModules(new Set());
      } else {
        return;
      }
    }
    setEditMode(!editMode);
  }, [editMode, hasUnsavedChanges, discardChanges]);

  // Handle module edit (from node click)
  const handleModuleEdit = useCallback((module: ArchitectureModule) => {
    setSelectedModule(module);
    setShowEditModal(true);
  }, []);

  // Handle module update from modal
  const handleModuleUpdate = useCallback((updatedModule: ArchitectureModule) => {
    if (selectedModule) {
      updateModule(selectedModule.filename, updatedModule);
    }
    setShowEditModal(false);
    setSelectedModule(null);
  }, [selectedModule, updateModule]);

  // Handle module delete
  const handleModuleDelete = useCallback((filename: string) => {
    deleteModule(filename);
    setShowEditModal(false);
    setSelectedModule(null);
  }, [deleteModule]);

  // Handle add module
  const handleAddModule = useCallback((module: ArchitectureModule) => {
    addModule(module);
  }, [addModule]);

  // Handle group toggle (expand/collapse)
  const handleToggleGroup = useCallback((groupName: string) => {
    setExpandedGroups(prev => {
      const next = new Set(prev);
      if (next.has(groupName)) {
        next.delete(groupName);
      } else {
        next.add(groupName);
      }
      return next;
    });
  }, []);

  // Handle group edit button click
  const handleEditGroupClick = useCallback((groupName: string) => {
    setEditingGroupName(groupName);
    setShowGroupModal(true);
  }, []);

  // Handle group save from modal (assigns modules to the group in one history entry)
  const handleGroupSave = useCallback((groupName: string, moduleFilenames: string[]) => {
    const filenameSet = new Set(moduleFilenames);
    // When creating a new group that matches an existing group name, treat as an edit
    // so stale members of that group are cleared if they weren't re-selected
    const effectiveOldGroupName = editingGroupName || groupName;
    const updatedModules = editableArchitecture.map(m => {
      if (filenameSet.has(m.filename)) {
        return { ...m, group: groupName };
      }
      // Clear group if this module was in the old group but wasn't re-selected
      if (m.group === effectiveOldGroupName) {
        return { ...m, group: undefined };
      }
      return m;
    });
    batchUpdateModules(updatedModules);
    // Auto-expand the new/edited group
    setExpandedGroups(prev => new Set([...prev, groupName]));
    setEditingGroupName(null);
  }, [editableArchitecture, editingGroupName, batchUpdateModules]);

  // Handle dependency add (from edge creation)
  const handleDependencyAdd = useCallback((targetFilename: string, sourceFilename: string) => {
    addDependency(targetFilename, sourceFilename);
  }, [addDependency]);

  // Handle dependency remove (from edge deletion)
  const handleDependencyRemove = useCallback((targetFilename: string, sourceFilename: string) => {
    removeDependency(targetFilename, sourceFilename);
  }, [removeDependency]);

  // Handle positions change (from node drag - updates all positions at once)
  const handlePositionsChange = useCallback((positions: Map<string, { x: number; y: number }>) => {
    updatePositions(positions);
  }, [updatePositions]);

  // Handle initial positions calculated by Dagre (before entering edit mode)
  // This updates the base architecture state so positions are available when saving
  const handleInitialPositionsCalculated = useCallback((positions: Map<string, { x: number; y: number }>) => {
    if (!architecture) return;

    // Update architecture with calculated positions
    const updatedArchitecture = architecture.map((m) => {
      const pos = positions.get(m.filename);
      if (pos) {
        return { ...m, position: pos };
      }
      return m;
    });

    // Update both the base architecture and the history hook's original
    setArchitecture(updatedArchitecture);
  }, [architecture]);

  // Validate and save architecture
  const handleSaveArchitecture = useCallback(async () => {
    if (!editableArchitecture || editableArchitecture.length === 0) return;

    setIsSaving(true);
    setValidationResult(null);
    setHighlightedModules(new Set());

    try {
      // Validate first
      const validation = await api.validateArchitecture(editableArchitecture);
      setValidationResult(validation);

      if (!validation.valid) {
        // Highlight modules with errors
        const modulesToHighlight = new Set<string>();
        for (const error of validation.errors) {
          error.modules.forEach((m) => modulesToHighlight.add(m));
        }
        setHighlightedModules(modulesToHighlight);
        setIsSaving(false);
        return;
      }

      // Save to file
      const result = await api.saveArchitecture(editableArchitecture);
      if (result.success) {
        // Update the base architecture state
        setArchitecture(editableArchitecture);
        setOriginal(editableArchitecture);
        setEditMode(false);
      } else {
        alert('Failed to save: ' + (result.error || 'Unknown error'));
      }
    } catch (e: any) {
      console.error('Failed to save architecture:', e);
      alert('Failed to save: ' + e.message);
    } finally {
      setIsSaving(false);
    }
  }, [editableArchitecture, setOriginal]);

  // Discard changes
  const handleDiscardChanges = useCallback(() => {
    if (hasUnsavedChanges) {
      const shouldDiscard = window.confirm('Are you sure you want to discard all changes?');
      if (!shouldDiscard) return;
    }
    discardChanges();
    setRearrangeVersion(v => v + 1);  // force React Flow to resync with reverted positions
    setValidationResult(null);
    setHighlightedModules(new Set());
  }, [hasUnsavedChanges, discardChanges, setRearrangeVersion]);

  // Re-arrange graph layout via agentic workflow
  const handleRearrange = useCallback(async () => {
    setIsRearranging(true);
    try {
      const result = await api.rearrangeGraphLayout(architecturePathInput);
      if (result.success && result.modules) {
        const positions = new Map<string, { x: number; y: number }>();
        for (const mod of result.modules) {
          if (mod.position) {
            positions.set(mod.filename, mod.position);
          }
        }
        if (positions.size > 0) {
          updatePositions(positions);
          setRearrangeVersion(v => v + 1);
        }
      } else {
        alert('Re-arrange failed: ' + (result.error || 'Unknown error'));
      }
    } catch (e: any) {
      console.error('Re-arrange failed:', e);
      alert('Re-arrange failed: ' + e.message);
    } finally {
      setIsRearranging(false);
    }
  }, [updatePositions, architecturePathInput]);

  // Keyboard shortcuts
  useEffect(() => {
    const handleKeyDown = (e: KeyboardEvent) => {
      // Only handle shortcuts in edit mode
      if (!editMode) return;

      // Ctrl/Cmd + S to save
      if ((e.ctrlKey || e.metaKey) && e.key === 's') {
        e.preventDefault();
        if (hasUnsavedChanges) {
          handleSaveArchitecture();
        }
      }

      // Ctrl/Cmd + Z to undo
      if ((e.ctrlKey || e.metaKey) && e.key === 'z' && !e.shiftKey) {
        e.preventDefault();
        if (canUndo) {
          undo();
        }
      }

      // Ctrl/Cmd + Shift + Z to redo
      if ((e.ctrlKey || e.metaKey) && e.key === 'z' && e.shiftKey) {
        e.preventDefault();
        if (canRedo) {
          redo();
        }
      }

      // Escape to exit edit mode
      if (e.key === 'Escape') {
        if (showEditModal) {
          setShowEditModal(false);
          setSelectedModule(null);
        } else if (showAddModal) {
          setShowAddModal(false);
        } else if (hasUnsavedChanges) {
          handleDiscardChanges();
        } else {
          setEditMode(false);
        }
      }

      // N to add new module
      if (e.key === 'n' && !e.ctrlKey && !e.metaKey && !showEditModal && !showAddModal) {
        // Don't trigger if typing in an input
        if ((e.target as HTMLElement).tagName === 'INPUT' || (e.target as HTMLElement).tagName === 'TEXTAREA') {
          return;
        }
        e.preventDefault();
        setShowAddModal(true);
      }
    };

    window.addEventListener('keydown', handleKeyDown);
    return () => window.removeEventListener('keydown', handleKeyDown);
  }, [
    editMode,
    hasUnsavedChanges,
    canUndo,
    canRedo,
    showEditModal,
    showAddModal,
    handleSaveArchitecture,
    handleDiscardChanges,
    undo,
    redo,
  ]);

  // Warn before leaving with unsaved changes
  useEffect(() => {
    const handleBeforeUnload = (e: BeforeUnloadEvent) => {
      if (editMode && hasUnsavedChanges) {
        e.preventDefault();
        e.returnValue = '';
      }
    };

    window.addEventListener('beforeunload', handleBeforeUnload);
    return () => window.removeEventListener('beforeunload', handleBeforeUnload);
  }, [editMode, hasUnsavedChanges]);

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
            Generate a new architecture from a GitHub issue, or load an existing architecture.json file.
          </p>

          {/* GitHub Issue URL option */}
          <div className="mb-6">
            <p className="text-surface-500 text-xs mb-3">Generate from a GitHub issue</p>
            <div className="flex gap-2">
              <input
                type="text"
                value={issueUrl}
                onChange={(e) => {
                  setIssueUrl(e.target.value);
                  setIssueGenerationError(null);
                }}
                placeholder="https://github.com/org/repo/issues/123"
                className="flex-1 px-3 py-2 bg-surface-900/50 border border-surface-600 rounded-lg text-sm text-white placeholder-surface-500 focus:outline-none focus:border-accent-500"
                disabled={!serverConnected || isGeneratingFromIssue}
                onKeyDown={(e) => {
                  if (e.key === 'Enter') handleGenerateFromIssue();
                }}
              />
              <button
                onClick={handleGenerateFromIssue}
                className={`px-4 py-2 rounded-lg text-sm font-medium transition-colors ${
                  isGeneratingFromIssue
                    ? 'bg-surface-600 text-surface-400 cursor-not-allowed'
                    : 'bg-accent-600 hover:bg-accent-500 text-white'
                }`}
                disabled={!serverConnected || isGeneratingFromIssue || !issueUrl.trim()}
              >
                {isGeneratingFromIssue ? 'Starting...' : 'Generate'}
              </button>
            </div>
            {issueGenerationError && (
              <p className="text-red-400 text-xs mt-2">{issueGenerationError}</p>
            )}
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
                onClick={() => setShowFileBrowser('architecture')}
                className="p-2 bg-surface-700 hover:bg-surface-600 text-surface-400 hover:text-white rounded-lg transition-colors"
                disabled={!serverConnected}
                title="Browse files"
              >
                <svg className="w-5 h-5" fill="none" stroke="currentColor" viewBox="0 0 24 24">
                  <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M3 7v10a2 2 0 002 2h14a2 2 0 002-2V9a2 2 0 00-2-2h-6l-2-2H5a2 2 0 00-2 2z" />
                </svg>
              </button>
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
            filter=".json"
            title="Select Architecture File"
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
              {/* Generate Prompts Button - only when architecture exists */}
              {architecture && architecture.length > 0 && (
                <div className="p-3 border-t border-surface-700/50">
                  <button
                    onClick={handleGeneratePrompts}
                    disabled={isGeneratingPrompts || isExecuting || !serverConnected}
                    className={`w-full px-4 py-2.5 rounded-xl font-medium transition-all duration-200 flex items-center justify-center gap-2 ${
                      isGeneratingPrompts || isExecuting || !serverConnected
                        ? 'bg-surface-700 text-surface-500 cursor-not-allowed'
                        : 'bg-gradient-to-r from-emerald-600 to-emerald-500 hover:from-emerald-500 hover:to-emerald-400 text-white shadow-lg shadow-emerald-500/25'
                    }`}
                  >
                    {isGeneratingPrompts ? (
                      <svg className="animate-spin h-4 w-4" viewBox="0 0 24 24">
                        <circle className="opacity-25" cx="12" cy="12" r="10" stroke="currentColor" strokeWidth="4" fill="none" />
                        <path className="opacity-75" fill="currentColor" d="M4 12a8 8 0 018-8V0C5.373 0 0 5.373 0 12h4z" />
                      </svg>
                    ) : (
                      <svg className="w-4 h-4" fill="none" stroke="currentColor" viewBox="0 0 24 24">
                        <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M9 12h6m-6 4h6m2 5H7a2 2 0 01-2-2V5a2 2 0 012-2h5.586a1 1 0 01.707.293l5.414 5.414a1 1 0 01.293.707V19a2 2 0 01-2 2z" />
                      </svg>
                    )}
                    {isGeneratingPrompts ? 'Generating...' : 'Generate Prompts'}
                  </button>
                </div>
              )}

              {/* Sync All/Remaining Button */}
              {architecture && architecture.length > 0 && onAddToQueue && (
                <div className="p-3 border-t border-surface-700/50">
                  <button
                    onClick={handleSyncAll}
                    disabled={remainingModulesCount === 0}
                    className={`w-full px-4 py-2.5 rounded-xl font-medium transition-all duration-200 flex items-center justify-center gap-2 ${
                      remainingModulesCount === 0
                        ? 'bg-surface-700 text-surface-500 cursor-not-allowed'
                        : 'bg-gradient-to-r from-blue-600 to-blue-500 hover:from-blue-500 hover:to-blue-400 text-white shadow-lg shadow-blue-500/25'
                    }`}
                  >
                    <svg className="w-4 h-4" fill="none" stroke="currentColor" viewBox="0 0 24 24">
                      <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M4 4v5h.582m15.356 2A8.001 8.001 0 004.582 9m0 0H9m11 11v-5h-.581m0 0a8.003 8.003 0 01-15.357-2m15.357 2H15" />
                    </svg>
                    {remainingModulesCount === 0
                      ? 'All Synced'
                      : remainingModulesCount === architecture.length
                        ? `Sync All (${remainingModulesCount})`
                        : `Sync Remaining (${remainingModulesCount})`
                    }
                  </button>
                </div>
              )}

              {/* Batch Filter & Sync - only show if multiple batches exist */}
              {batches.length > 1 && onAddToQueue && (
                <div className="p-3 border-t border-surface-700/50">
                  <p className="text-xs font-medium text-surface-400 uppercase tracking-wider mb-2">Sync by Batch</p>
                  <BatchFilterDropdown
                    batches={batches}
                    selectedBatch={selectedBatch}
                    onSelectBatch={setSelectedBatch}
                    onSyncBatch={handleSyncBatch}
                    remainingCountByBatch={remainingCountByBatch}
                    showModuleList
                  />
                </div>
              )}

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
                      onClick={() => setShowFileBrowser('architecture')}
                      className="p-1.5 bg-surface-700 hover:bg-surface-600 text-surface-400 hover:text-white rounded transition-colors"
                      title="Browse files"
                    >
                      <svg className="w-4 h-4" fill="none" stroke="currentColor" viewBox="0 0 24 24">
                        <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M3 7v10a2 2 0 002 2h14a2 2 0 002-2V9a2 2 0 00-2-2h-6l-2-2H5a2 2 0 00-2 2z" />
                      </svg>
                    </button>
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

              {/* Start New Project */}
              <div className="border-t border-surface-700/50">
                <div className="p-3">
                  <button
                    onClick={() => {
                      // Reset all state and go back to empty mode
                      setArchitecture(null);
                      setPrdContent('');
                      setAppName('');
                      setMode('empty');
                      setEditMode(false);
                    }}
                    className="w-full px-3 py-2 bg-surface-800/50 hover:bg-surface-700 text-surface-400 hover:text-white rounded-lg text-xs font-medium transition-colors flex items-center justify-center gap-2"
                    title="Start a new project from scratch"
                  >
                    <svg className="w-4 h-4" fill="none" stroke="currentColor" viewBox="0 0 24 24">
                      <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M12 4v16m8-8H4" />
                    </svg>
                    Start New Project
                  </button>
                </div>
              </div>
            </>
          )}
        </div>
      </div>

      {/* Main Content - Architecture Graph */}
      <div className="flex-1 min-w-0 flex flex-col">
        {/* Graph Toolbar - only show in graph mode */}
        {mode === 'graph' && displayArchitecture && (
          <GraphToolbar
            editMode={editMode}
            hasUnsavedChanges={hasUnsavedChanges}
            onToggleEditMode={handleToggleEditMode}
            onAddModule={() => setShowAddModal(true)}
            onSave={handleSaveArchitecture}
            onDiscard={handleDiscardChanges}
            onUndo={undo}
            onRedo={redo}
            canUndo={canUndo}
            canRedo={canRedo}
            isSaving={isSaving}
            onSyncFromPrompts={handleOpenSyncModal}
            onRearrange={handleRearrange}
            isRearranging={isRearranging}
            onManageGroups={editMode ? () => { setEditingGroupName(null); setShowGroupModal(true); } : undefined}
          />
        )}

        {/* Validation Errors Banner */}
        {validationResult && !validationResult.valid && (
          <div className="bg-red-500/10 border-b border-red-500/30 px-4 py-2">
            <div className="flex items-start gap-2">
              <svg className="w-4 h-4 text-red-400 flex-shrink-0 mt-0.5" fill="currentColor" viewBox="0 0 20 20">
                <path fillRule="evenodd" d="M18 10a8 8 0 11-16 0 8 8 0 0116 0zm-7 4a1 1 0 11-2 0 1 1 0 012 0zm-1-9a1 1 0 00-1 1v4a1 1 0 102 0V6a1 1 0 00-1-1z" clipRule="evenodd" />
              </svg>
              <div className="flex-1">
                <p className="text-sm text-red-400 font-medium">Cannot save: validation errors</p>
                <ul className="text-xs text-red-300 mt-1 space-y-0.5">
                  {validationResult.errors.map((err, i) => (
                    <li key={i}>{err.message}</li>
                  ))}
                </ul>
              </div>
            </div>
          </div>
        )}

        <div className="flex-1 min-h-0">
          {mode === 'graph' && displayArchitecture ? (
            isMobile ? (
              // Mobile fallback - simplified list view
              <div className="glass rounded-xl border border-surface-700/50 h-full overflow-y-auto p-4">
                <div className="text-center mb-6">
                  <svg className="w-12 h-12 mx-auto mb-3 text-surface-400" fill="none" stroke="currentColor" viewBox="0 0 24 24">
                    <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={1.5} d="M9.75 17L9 20l-1 1h8l-1-1-.75-3M3 13h18M5 17h14a2 2 0 002-2V5a2 2 0 00-2-2H5a2 2 0 00-2 2v10a2 2 0 002 2z" />
                  </svg>
                  <h3 className="text-white font-semibold mb-2">Architecture Graph</h3>
                  <p className="text-sm text-surface-400 mb-4">
                    The interactive architecture graph is best viewed on desktop devices (screen width &gt; 768px)
                  </p>
                  <div className="flex items-center justify-center gap-2 text-xs text-surface-500">
                    <svg className="w-4 h-4" fill="none" stroke="currentColor" viewBox="0 0 24 24">
                      <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M13 16h-1v-4h-1m1-4h.01M21 12a9 9 0 11-18 0 9 9 0 0118 0z" />
                    </svg>
                    <span>Module list shown below</span>
                  </div>
                </div>
                <div className="space-y-3">
                  {displayArchitecture.map((module) => (
                    <div
                      key={module.filename}
                      className="bg-surface-800/50 p-4 rounded-lg border border-surface-700/30 hover:border-surface-600/50 transition-colors"
                      onClick={() => handleModuleClick(module)}
                    >
                      <div className="flex items-start justify-between gap-3 mb-2">
                        <div className="font-medium text-white text-sm flex-1">{module.filename}</div>
                        {existingPrompts.has(`${module.filename.replace('.py', '')}.prompt`) && (
                          <span className="inline-flex items-center gap-1 px-2 py-0.5 rounded-full text-[10px] font-medium bg-green-500/10 text-green-400 border border-green-500/20 flex-shrink-0">
                            <svg className="w-3 h-3" fill="currentColor" viewBox="0 0 20 20">
                              <path fillRule="evenodd" d="M16.707 5.293a1 1 0 010 1.414l-8 8a1 1 0 01-1.414 0l-4-4a1 1 0 011.414-1.414L8 12.586l7.293-7.293a1 1 0 011.414 0z" clipRule="evenodd" />
                            </svg>
                            Prompt exists
                          </span>
                        )}
                      </div>
                      <p className="text-xs text-surface-400 line-clamp-2 mb-3">{module.description}</p>
                      {module.dependencies && module.dependencies.length > 0 && (
                        <div className="flex items-center gap-1.5 text-xs text-surface-500">
                          <svg className="w-3.5 h-3.5 flex-shrink-0" fill="none" stroke="currentColor" viewBox="0 0 24 24">
                            <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M13 7l5 5m0 0l-5 5m5-5H6" />
                          </svg>
                          <span className="truncate">Depends on: {module.dependencies.join(', ')}</span>
                        </div>
                      )}
                    </div>
                  ))}
                </div>
                {!editMode && (
                  <button
                    onClick={() => handleGeneratePrompts()}
                    disabled={isGeneratingPrompts}
                    className="mt-6 w-full px-4 py-3 bg-gradient-to-r from-accent-600 to-accent-500 hover:from-accent-500 hover:to-accent-400 text-white rounded-xl font-medium transition-all duration-200 shadow-lg shadow-accent-500/25 hover:shadow-accent-500/40 disabled:opacity-50 disabled:cursor-not-allowed"
                  >
                    {isGeneratingPrompts ? 'Generating Prompts...' : 'Generate All Prompts'}
                  </button>
                )}
              </div>
            ) : (
              // Desktop - full interactive graph
              <DependencyViewer
                architecture={displayArchitecture}
                prdContent={prdContent}
                appName={appName}
                onModuleClick={handleModuleClick}
                onRunSync={handleRunSyncForModule}
                onGeneratePrompts={handleGeneratePrompts}
                isGeneratingPrompts={isGeneratingPrompts}
                existingPrompts={existingPrompts}
                promptsInfo={promptsInfo}
                editMode={editMode}
                onModuleEdit={handleModuleEdit}
                onModuleDelete={handleModuleDelete}
                onDependencyAdd={handleDependencyAdd}
                onDependencyRemove={handleDependencyRemove}
                onPositionsChange={handlePositionsChange}
                highlightedModules={highlightedModules}
                onInitialPositionsCalculated={handleInitialPositionsCalculated}
                batches={batches}
                selectedBatch={selectedBatch}
                onBatchSelect={setSelectedBatch}
                onSyncBatch={handleSyncBatch}
                remainingCountByBatch={remainingCountByBatch}
                rearrangeVersion={rearrangeVersion}
                expandedGroups={expandedGroups}
                onToggleGroup={handleToggleGroup}
                onEditGroup={editMode ? handleEditGroupClick : undefined}
              />
            )
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
      </div>

      {/* File Browser Modal */}
      {showFileBrowser && (
        <FileBrowser
          onSelect={handleFileSelect}
          onClose={() => setShowFileBrowser(null)}
          filter={showFileBrowser === 'architecture' ? '.json' : '.md'}
          title={
            showFileBrowser === 'prd'
              ? 'Select PRD File'
              : showFileBrowser === 'architecture'
              ? 'Select Architecture File'
              : 'Select Tech Stack File'
          }
        />
      )}

      {/* Prompt Order Selection Modal */}
      {showOrderModal && architecture && (
        <PromptOrderModal
          isOpen={showOrderModal}
          modules={architecture}
          existingPrompts={existingPrompts}
          globalOptions={globalOptions}
          onGlobalOptionsChange={setGlobalOptions}
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

      {/* Module Edit Modal */}
      <ModuleEditModal
        isOpen={showEditModal}
        module={selectedModule}
        allModules={editableArchitecture}
        onSave={handleModuleUpdate}
        onDelete={handleModuleDelete}
        onClose={() => {
          setShowEditModal(false);
          setSelectedModule(null);
        }}
      />

      {/* Group Edit Modal */}
      <GroupEditModal
        isOpen={showGroupModal}
        groupName={editingGroupName}
        allModules={editableArchitecture}
        onSave={handleGroupSave}
        onClose={() => {
          setShowGroupModal(false);
          setEditingGroupName(null);
        }}
      />

      {/* Add Module Modal */}
      <AddModuleModal
        isOpen={showAddModal}
        existingModules={editableArchitecture}
        onAdd={handleAddModule}
        onClose={() => setShowAddModal(false)}
      />

      {/* Sync from Prompts Modal */}
      <SyncFromPromptModal
        isOpen={showSyncModal}
        isSyncing={isSyncing}
        result={syncResult}
        onSync={handleSync}
        onClose={handleCloseSyncModal}
      />

      {/* Sync Options Modal (for running pdd sync with options) */}
      <SyncOptionsModal
        isOpen={showSyncOptionsModal}
        title={
          pendingSyncAll
            ? `Sync ${remainingModulesCount} Module${remainingModulesCount !== 1 ? 's' : ''}`
            : pendingSyncBatch
              ? `Sync ${pendingSyncBatch.name} (${remainingCountByBatch.get(pendingSyncBatch.id) || 0} modules)`
              : 'Sync Module'
        }
        description={
          pendingSyncAll
            ? 'Configure options for syncing all remaining modules'
            : pendingSyncBatch
              ? `Configure options for syncing modules in ${pendingSyncBatch.name} (sorted by priority)`
              : `Configure options for syncing ${pendingSyncModule?.filename || 'module'}`
        }
        onConfirm={handleSyncOptionsConfirm}
        onAddToQueue={onAddToQueue ? handleSyncOptionsAddToQueue : undefined}
        onClose={() => {
          setShowSyncOptionsModal(false);
          setPendingSyncModule(null);
          setPendingSyncAll(false);
          setPendingSyncBatch(null);
        }}
      />
    </div>
  );
};

export default ArchitectureView;
