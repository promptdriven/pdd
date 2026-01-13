import React, { useState, useEffect, useCallback } from 'react';
import { CommandType } from './types';
import { COMMANDS } from './constants';
import PromptSelector from './components/PromptSelector';
import PromptSpace from './components/PromptSpace';
import ArchitectureView from './components/ArchitectureView';
import ProjectSettings from './components/ProjectSettings';
import JobDashboard, { BatchOperation } from './components/JobDashboard';
import TaskQueuePanel from './components/TaskQueuePanel';
import AddToQueueModal from './components/AddToQueueModal';
import AuthStatusIndicator from './components/AuthStatusIndicator';
import ReauthModal from './components/ReauthModal';
import ErrorBoundary from './components/ErrorBoundary';
import { api, PromptInfo, RunResult, CommandRequest } from './api';
import { Squares2X2Icon, DocumentTextIcon, BugAntIcon, Cog6ToothIcon } from './components/Icon';
import { useJobs, JobInfo } from './hooks/useJobs';
import { useTaskQueue } from './hooks/useTaskQueue';
import { useToast } from './components/Toast';

type View = 'architecture' | 'prompts' | 'bug' | 'settings';

// Parse URL hash to get initial view and prompt path
const parseHash = (): { view: View; promptPath?: string } => {
  const hash = window.location.hash.slice(1); // Remove #
  if (!hash) return { view: 'architecture' };

  const [viewPart, ...promptParts] = hash.split('/');
  const promptPath = promptParts.length > 0 ? promptParts.join('/') : undefined;

  const validViews: View[] = ['architecture', 'prompts', 'bug', 'settings'];
  const view = validViews.includes(viewPart as View) ? (viewPart as View) : 'architecture';

  return { view, promptPath };
};

const App: React.FC = () => {
  const initialState = parseHash();
  const [view, setView] = useState<View>(initialState.view);
  const [pendingPromptPath, setPendingPromptPath] = useState<string | undefined>(initialState.promptPath);
  const [selectedPrompt, setSelectedPrompt] = useState<PromptInfo | null>(null);
  const [editingPrompt, setEditingPrompt] = useState<PromptInfo | null>(null);
  const [isExecuting, setIsExecuting] = useState(false);
  const [executionStatus, setExecutionStatus] = useState<'idle' | 'running' | 'success' | 'failed'>('idle');
  const [lastCommand, setLastCommand] = useState<string | null>(null);
  const [lastRunResult, setLastRunResult] = useState<RunResult | null>(null);
  const [serverConnected, setServerConnected] = useState(false);

  // Bug command state
  const [bugIssueUrl, setBugIssueUrl] = useState('');

  // Batch operation state (for architecture prompt generation)
  const [batchOperation, setBatchOperation] = useState<BatchOperation | null>(null);

  // Auth modal state
  const [showReauthModal, setShowReauthModal] = useState(false);

  // Add to queue modal state
  const [showAddToQueueModal, setShowAddToQueueModal] = useState(false);
  const [addToQueuePrompt, setAddToQueuePrompt] = useState<PromptInfo | null>(null);

  // Toast notifications
  const { addToast } = useToast();

  // Task queue for sequential execution
  const taskQueue = useTaskQueue({
    onTaskStart: (task) => {
      addToast(`Starting task: ${task.displayCommand}`, 'info', 3000);
    },
    onTaskComplete: (task, success) => {
      addToast(
        `Task ${success ? 'completed' : 'failed'}: ${task.displayCommand}`,
        success ? 'success' : 'error',
        5000
      );
    },
    onQueueComplete: () => {
      addToast('Task queue completed', 'success', 3000);
    },
  });

  // Job management for multi-session support
  const handleJobComplete = useCallback((job: JobInfo, success: boolean) => {
    addToast(
      `${job.displayCommand} ${success ? 'completed successfully' : 'failed'}`,
      success ? 'success' : 'error',
      5000
    );
    // Notify task queue if this job was part of the queue
    taskQueue.handleJobComplete(job.id, success);
  }, [addToast, taskQueue]);

  const {
    activeJobs,
    completedJobs,
    selectedJob,
    selectedJobId,
    isAnyJobRunning,
    submitJob,
    cancelJob,
    removeJob,
    clearCompletedJobs,
    setSelectedJobId,
    addSpawnedJob,
    markSpawnedJobDone,
  } = useJobs({ onJobComplete: handleJobComplete });

  // Create a spawnTerminal-based job runner for the task queue
  // This matches how handleRunCommand works - spawns a new terminal window
  const spawnTerminalJob = useCallback(async (
    request: CommandRequest,
    displayCommand: string
  ): Promise<string | null> => {
    try {
      const result = await api.spawnTerminal(request);
      if (result.success && result.job_id) {
        // Add to job dashboard for tracking
        addSpawnedJob(displayCommand, request.command, result.job_id);
        return result.job_id;
      } else {
        console.error('Failed to spawn terminal:', result.message);
        return null;
      }
    } catch (error) {
      console.error('Failed to spawn terminal:', error);
      return null;
    }
  }, [addSpawnedJob]);

  // Connect the spawnTerminal job runner to the task queue
  useEffect(() => {
    taskQueue.setSubmitJob(spawnTerminalJob);
  }, [taskQueue, spawnTerminalJob]);

  // Handler to add task to queue
  const handleAddToQueue = useCallback((
    command: string,
    prompt: PromptInfo | null,
    request: CommandRequest,
    displayCommand: string
  ) => {
    taskQueue.addTask(command, prompt, request, displayCommand);
    addToast(`Added to queue: ${displayCommand}`, 'info', 3000);
  }, [taskQueue, addToast]);

  // Handler to open add to queue modal
  const handleOpenAddToQueueModal = useCallback((prompt: PromptInfo) => {
    setAddToQueuePrompt(prompt);
    setShowAddToQueueModal(true);
  }, []);

  // Check server connection on mount
  useEffect(() => {
    api.getStatus()
      .then(() => setServerConnected(true))
      .catch(() => setServerConnected(false));
  }, []);

  // Update URL hash when view or editingPrompt changes
  useEffect(() => {
    if (editingPrompt) {
      window.location.hash = `prompts/${editingPrompt.prompt}`;
    } else {
      window.location.hash = view;
    }
  }, [view, editingPrompt]);

  // Handle browser back/forward navigation
  useEffect(() => {
    const handleHashChange = () => {
      const { view: newView, promptPath } = parseHash();
      setView(newView);
      if (promptPath) {
        setPendingPromptPath(promptPath);
      } else {
        setEditingPrompt(null);
      }
    };

    window.addEventListener('hashchange', handleHashChange);
    return () => window.removeEventListener('hashchange', handleHashChange);
  }, []);

  // Load pending prompt path (from URL) when server connects
  useEffect(() => {
    if (serverConnected && pendingPromptPath) {
      api.listPrompts().then(prompts => {
        const found = prompts.find(p => p.prompt === pendingPromptPath);
        if (found) {
          setEditingPrompt(found);
        }
        setPendingPromptPath(undefined);
      }).catch(() => {
        setPendingPromptPath(undefined);
      });
    }
  }, [serverConnected, pendingPromptPath]);

  const handleRunCommand = async (command: CommandType, prompt: PromptInfo, commandOptions?: Record<string, any>) => {
    if (!serverConnected) {
      alert('Server not connected. Run "pdd connect" in your terminal first.');
      return;
    }

    const config = COMMANDS[command];
    setIsExecuting(true);
    setExecutionStatus('running');

    // Extract file paths from modal options (prefixed with _)
    // These override the auto-detected prompt.code and prompt.test
    const rawOptions = commandOptions || {};
    const codeFile = rawOptions['_code'] || prompt.code;
    const testFile = rawOptions['_test'] || prompt.test;

    // Build clean options for CLI:
    // 1. Remove internal prefixed keys (_code, _test)
    // 2. Transform _global_* keys to their actual flag names (e.g., _global_strength -> strength)
    const options: Record<string, any> = {};
    for (const [key, value] of Object.entries(rawOptions)) {
      if (key === '_code' || key === '_test') {
        // Skip internal file path keys - these are used for positional args
        continue;
      } else if (key.startsWith('_global_')) {
        // Strip _global_ prefix for CLI flags
        const actualKey = key.replace('_global_', '');
        options[actualKey] = value;
      } else {
        options[key] = value;
      }
    }

    // For sync, show basename; for others, show prompt path
    const displayArg = command === CommandType.SYNC ? prompt.sync_basename : prompt.prompt;
    // Build display command with options (for UI display only)
    const optionsStr = Object.keys(options).length > 0
      ? ' ' + Object.entries(options).map(([k, v]) => {
          if (typeof v === 'boolean') return v ? `--${k.replace(/_/g, '-')}` : '';
          return `--${k.replace(/_/g, '-')} ${v}`;
        }).filter(Boolean).join(' ')
      : '';
    const fullDisplayCommand = `pdd ${config.backendName} ${displayArg}${optionsStr}`;
    setLastCommand(fullDisplayCommand);

    try {
      // Build the command request based on command type
      const args: Record<string, any> = {};

      // For sync command, use sync_basename (without language suffix)
      // e.g., "calculator" not "calculator_python"
      if (command === CommandType.SYNC) {
        args.basename = prompt.sync_basename;
        // Pass context to ensure sync finds the prompt in the correct location
        if (prompt.context) {
          options['context'] = prompt.context;
        }
      } else if (command === CommandType.UPDATE) {
        // Update command: pdd update [PROMPT_FILE] <CODE_FILE> [ORIGINAL_CODE_FILE]
        // - If only code: generates new prompt for the code
        // - If prompt + code: updates prompt based on code changes
        // Pass as positional args tuple
        if (codeFile) {
          args.args = [prompt.prompt, codeFile];
        } else {
          // No code file - run in repo-wide mode (no file arguments)
          // This scans the entire repo and updates all prompts
          args.args = [];
        }
      } else if (command === CommandType.GENERATE) {
        args.prompt_file = prompt.prompt;
      } else if (command === CommandType.TEST) {
        args.prompt_file = prompt.prompt;
        args.code_file = codeFile;
      } else if (command === CommandType.EXAMPLE) {
        args.prompt_file = prompt.prompt;
        args.code_file = codeFile;
      } else if (command === CommandType.FIX) {
        args.prompt_file = prompt.prompt;
        args.code_file = codeFile;
        args.unit_test_files = testFile;
        // error_file is entered in options modal but is a positional arg
        if (options['error-file']) {
          args.error_file = options['error-file'];
          delete options['error-file'];
        }
      } else if (command === CommandType.SPLIT) {
        // Split command: pdd split INPUT_PROMPT INPUT_CODE EXAMPLE_CODE [--output-sub] [--output-modified]
        // - INPUT_PROMPT: selected prompt file
        // - INPUT_CODE: code file from _code field (codeFile)
        // - EXAMPLE_CODE: from example-code option
        args.input_prompt = prompt.prompt;
        args.input_code = codeFile;
        if (options['example-code']) {
          args.example_code = options['example-code'];
          delete options['example-code'];
        }
      } else if (command === CommandType.CHANGE) {
        // Change command: pdd change CHANGE_PROMPT_FILE INPUT_CODE [INPUT_PROMPT_FILE] [--budget] [--output]
        // - CHANGE_PROMPT_FILE: from change-prompt option
        // - INPUT_CODE: code file from _code field (codeFile)
        // - INPUT_PROMPT_FILE: selected prompt file (the prompt being modified)
        if (options['change-prompt']) {
          args.change_prompt_file = options['change-prompt'];
          delete options['change-prompt'];
        }
        args.input_code = codeFile;
        args.input_prompt_file = prompt.prompt;
      } else if (command === CommandType.DETECT) {
        // Detect command: pdd detect [PROMPT_FILES...] CHANGE_FILE [--output]
        // This command doesn't use the selected prompt (requiresPrompt: false)
        // All args come from modal options
        const promptFilesStr = options['prompt-files'] || '';
        const changeFile = options['change-file'] || '';
        // Parse comma-separated prompt files and add change file at the end
        const promptFiles = promptFilesStr.split(',').map((f: string) => f.trim()).filter(Boolean);
        args.args = [...promptFiles, changeFile].filter(Boolean);
        delete options['prompt-files'];
        delete options['change-file'];
      } else if (command === CommandType.AUTO_DEPS) {
        // Auto-deps command: pdd auto-deps PROMPT_FILE DIRECTORY_PATH [--output] [--csv] [--force-scan]
        args.prompt_file = prompt.prompt;
        if (options['directory-path']) {
          args.directory_path = options['directory-path'];
          delete options['directory-path'];
        }
      } else if (command === CommandType.CONFLICTS) {
        // Conflicts command: pdd conflicts PROMPT1 PROMPT2 [--output]
        args.prompt_file = prompt.prompt;
        if (options['prompt2']) {
          args.prompt2 = options['prompt2'];
          delete options['prompt2'];
        }
      } else if (command === CommandType.PREPROCESS) {
        // Preprocess command: pdd preprocess PROMPT_FILE [--output] [--xml] [--recursive] [--double]
        args.prompt_file = prompt.prompt;
      } else if (command === CommandType.CRASH) {
        // Crash command: pdd crash PROMPT_FILE CODE_FILE PROGRAM_FILE ERROR_FILE [options]
        args.prompt_file = prompt.prompt;
        args.code_file = codeFile;
        if (options['program-file']) {
          args.program_file = options['program-file'];
          delete options['program-file'];
        }
        if (options['error-file']) {
          args.error_file = options['error-file'];
          delete options['error-file'];
        }
      } else if (command === CommandType.VERIFY) {
        // Verify command: pdd verify PROMPT_FILE CODE_FILE VERIFICATION_PROGRAM [options]
        args.prompt_file = prompt.prompt;
        args.code_file = codeFile;
        if (options['verification-program']) {
          args.verification_program = options['verification-program'];
          delete options['verification-program'];
        }
      } else if (command === CommandType.SUBMIT_EXAMPLE) {
        // Submit Example uses fix --loop --auto-submit under the hood
        args.prompt_file = prompt.prompt;
        args.code_file = codeFile;
        args.unit_test_files = testFile;
        // Create a placeholder error file path (loop mode doesn't require existing error file)
        args.error_file = '.pdd/submit_example_errors.log';
        // Force loop and auto-submit flags
        options['loop'] = true;
        options['auto-submit'] = true;
        // Move verification-program from options to args
        if (options['verification-program']) {
          args.verification_program = options['verification-program'];
          delete options['verification-program'];
        }
      }

      // Spawn command in a new terminal window for complete isolation
      const result = await api.spawnTerminal({
        command: config.backendName,
        args,
        options,
      });

      if (result.success) {
        // Add to job dashboard for tracking with server-provided job_id
        addSpawnedJob(fullDisplayCommand, config.backendName, result.job_id);
        setExecutionStatus('success');
        addToast(`Opened terminal: ${fullDisplayCommand}`, 'success', 3000);
      } else {
        setExecutionStatus('failed');
        addToast(`Failed to open terminal: ${result.message}`, 'error', 5000);
      }

      // Clear the status bar after a short delay
      setTimeout(() => {
        setExecutionStatus('idle');
        setLastCommand(null);
      }, 3000);
    } catch (error: any) {
      console.error('Failed to execute command:', error);
      setLastRunResult({
        success: false,
        message: error.message || 'Failed to execute command',
        exit_code: 1,
        error_details: error.message,
      });
      setExecutionStatus('failed');
      addToast(`Error: ${error.message}`, 'error', 5000);
      setTimeout(() => {
        setExecutionStatus('idle');
        setLastCommand(null);
      }, 10000);
    } finally {
      setIsExecuting(false);
    }
  };

  const handleRunBugCommand = async () => {
    if (!serverConnected) {
      alert('Server not connected. Run "pdd connect" in your terminal first.');
      return;
    }

    if (!bugIssueUrl.trim()) {
      alert('Please enter a GitHub issue URL');
      return;
    }

    setIsExecuting(true);
    setExecutionStatus('running');
    const displayCommand = `pdd bug ${bugIssueUrl}`;
    setLastCommand(displayCommand);

    try {
      // Spawn bug command in a new terminal window for complete isolation
      const result = await api.spawnTerminal({
        command: 'bug',
        args: { args: [bugIssueUrl] },
        options: {},
      });

      if (result.success) {
        // Add to job dashboard for tracking with server-provided job_id
        addSpawnedJob(displayCommand, 'bug', result.job_id);
        setExecutionStatus('success');
        addToast(`Opened terminal: ${displayCommand}`, 'success', 3000);
      } else {
        setExecutionStatus('failed');
        addToast(`Failed to open terminal: ${result.message}`, 'error', 5000);
      }

      setTimeout(() => {
        setExecutionStatus('idle');
        setLastCommand(null);
      }, 3000);
    } catch (error: any) {
      console.error('Failed to execute bug command:', error);
      setExecutionStatus('failed');
      addToast(`Error: ${error.message}`, 'error', 5000);
      setTimeout(() => {
        setExecutionStatus('idle');
        setLastCommand(null);
      }, 5000);
    } finally {
      setIsExecuting(false);
    }
  };

  // Handler for PromptSpace command execution
  const handlePromptSpaceCommand = (command: CommandType, options?: Record<string, any>) => {
    if (editingPrompt) {
      handleRunCommand(command, editingPrompt, options);
    }
  };

  // Cancel command handler for PromptSpace
  const handleCancelCommand = async () => {
    try {
      const result = await api.cancelCommand();
      if (result.cancelled) {
        setExecutionStatus('failed');
        setLastCommand(null);
        setTimeout(() => setExecutionStatus('idle'), 3000);
      }
    } catch (e) {
      console.error('Failed to cancel:', e);
    }
  };

  // Batch operation callbacks for ArchitectureView
  const handleBatchOperationStart = useCallback((name: string, total: number) => {
    setBatchOperation({
      id: `batch-${Date.now()}`,
      name,
      current: 0,
      total,
      currentItem: '',
      status: 'running',
      startedAt: new Date(),
    });
  }, []);

  const handleBatchOperationProgress = useCallback((current: number, total: number, currentItem: string) => {
    setBatchOperation(prev => prev ? {
      ...prev,
      current,
      total,
      currentItem,
    } : null);
  }, []);

  const handleBatchOperationComplete = useCallback((success: boolean) => {
    setBatchOperation(prev => prev ? {
      ...prev,
      status: success ? 'completed' : 'failed',
    } : null);
    // Clear after a short delay
    setTimeout(() => setBatchOperation(null), 3000);
  }, []);

  const handleCancelBatchOperation = useCallback(async () => {
    // This will trigger the cancel in ArchitectureView
    try {
      await api.cancelCommand();
    } catch (e) {
      console.error('Failed to cancel batch operation:', e);
    }
  }, []);

  // If editing a prompt, show full-screen PromptSpace
  if (editingPrompt) {
    return (
      <PromptSpace
        prompt={editingPrompt}
        onBack={() => setEditingPrompt(null)}
        onRunCommand={handlePromptSpaceCommand}
        isExecuting={isExecuting}
        executionStatus={executionStatus}
        lastCommand={lastCommand}
        lastRunResult={lastRunResult}
        onCancelCommand={handleCancelCommand}
      />
    );
  }

  return (
    <ErrorBoundary>
    <div className="min-h-screen bg-surface-950">
      {/* Modern responsive header */}
      <header className="glass sticky top-0 z-40 border-b border-surface-700/50">
        <div className="max-w-7xl mx-auto px-4 sm:px-6 lg:px-8">
          <div className="flex items-center justify-between h-16">
            {/* Logo - responsive sizing */}
            <div className="flex items-center gap-2 sm:gap-3 flex-shrink-0">
              <div className="w-8 h-8 sm:w-9 sm:h-9 rounded-lg bg-surface-800/80 flex items-center justify-center shadow-glow p-1">
                <svg viewBox="0 0 1024 1024" className="w-full h-full" xmlns="http://www.w3.org/2000/svg">
                  <defs>
                    <filter id="glow-header" x="-60%" y="-60%" width="220%" height="220%">
                      <feGaussianBlur in="SourceGraphic" stdDeviation="40" result="blur"/>
                      <feMerge>
                        <feMergeNode in="blur"/>
                        <feMergeNode in="SourceGraphic"/>
                      </feMerge>
                    </filter>
                  </defs>
                  <g stroke="#00e3ff" strokeWidth="60" strokeLinecap="round" strokeLinejoin="round" fill="none" filter="url(#glow-header)">
                    <path d="M 260 180 H 600 A 230 230 0 0 1 600 660 H 480 L 260 880 V 180 Z"/>
                    <polyline points="505 340 585 420 505 500"/>
                  </g>
                </svg>
              </div>
              <div className="hidden sm:block">
                <h1 className="text-base sm:text-lg font-bold text-white whitespace-nowrap">Prompt Driven Development</h1>
              </div>
            </div>

            {/* View switcher - centered on larger screens */}
            <div className="flex gap-1 sm:gap-2 bg-surface-800/50 p-1 rounded-xl">
              <button
                onClick={() => setView('architecture')}
                className={`px-3 sm:px-4 py-1.5 sm:py-2 rounded-lg text-xs sm:text-sm font-medium transition-all duration-200 ${
                  view === 'architecture'
                    ? 'bg-accent-600 text-white shadow-lg shadow-accent-500/25'
                    : 'text-surface-300 hover:text-white hover:bg-surface-700'
                }`}
              >
                <Squares2X2Icon className="hidden sm:inline w-4 h-4 mr-1" />Architecture
              </button>
              <button
                onClick={() => setView('prompts')}
                className={`px-3 sm:px-4 py-1.5 sm:py-2 rounded-lg text-xs sm:text-sm font-medium transition-all duration-200 ${
                  view === 'prompts'
                    ? 'bg-accent-600 text-white shadow-lg shadow-accent-500/25'
                    : 'text-surface-300 hover:text-white hover:bg-surface-700'
                }`}
              >
                <DocumentTextIcon className="hidden sm:inline w-4 h-4 mr-1" />Prompts
              </button>
              <button
                onClick={() => setView('bug')}
                className={`px-3 sm:px-4 py-1.5 sm:py-2 rounded-lg text-xs sm:text-sm font-medium transition-all duration-200 ${
                  view === 'bug'
                    ? 'bg-accent-600 text-white shadow-lg shadow-accent-500/25'
                    : 'text-surface-300 hover:text-white hover:bg-surface-700'
                }`}
              >
                <BugAntIcon className="hidden sm:inline w-4 h-4 mr-1" />Bug
              </button>
              <button
                onClick={() => setView('settings')}
                className={`px-3 sm:px-4 py-1.5 sm:py-2 rounded-lg text-xs sm:text-sm font-medium transition-all duration-200 ${
                  view === 'settings'
                    ? 'bg-accent-600 text-white shadow-lg shadow-accent-500/25'
                    : 'text-surface-300 hover:text-white hover:bg-surface-700'
                }`}
              >
                <Cog6ToothIcon className="hidden sm:inline w-4 h-4 mr-1" />Settings
              </button>
            </div>

            {/* Server status - responsive */}
            <div className={`flex items-center gap-1.5 sm:gap-2 text-xs sm:text-sm px-2 sm:px-3 py-1.5 rounded-full transition-colors ${
              serverConnected
                ? 'bg-green-500/10 text-green-400 border border-green-500/20'
                : 'bg-yellow-500/10 text-yellow-400 border border-yellow-500/20'
            }`}>
              <span className={`w-1.5 h-1.5 sm:w-2 sm:h-2 rounded-full ${serverConnected ? 'bg-green-400 animate-pulse-slow' : 'bg-yellow-400 animate-pulse'}`} />
              <span className="hidden xs:inline">{serverConnected ? 'Connected' : 'Offline'}</span>
            </div>

            {/* Cloud auth status */}
            <AuthStatusIndicator onReauth={() => setShowReauthModal(true)} />
          </div>
        </div>
      </header>

      {/* Status bar - modern glass effect */}
      {executionStatus !== 'idle' && (
        <div className={`
          px-4 sm:px-6 py-2.5 sm:py-3 text-center text-xs sm:text-sm font-medium border-b animate-slide-down
          ${executionStatus === 'running' ? 'bg-accent-500/10 text-accent-300 border-accent-500/20' : ''}
          ${executionStatus === 'success' ? 'bg-green-500/10 text-green-300 border-green-500/20' : ''}
          ${executionStatus === 'failed' ? 'bg-red-500/10 text-red-300 border-red-500/20' : ''}
        `}>
          {executionStatus === 'running' && (
            <span className="flex items-center justify-center gap-2 flex-wrap">
              <svg className="animate-spin h-4 w-4 flex-shrink-0" viewBox="0 0 24 24">
                <circle className="opacity-25" cx="12" cy="12" r="10" stroke="currentColor" strokeWidth="4" fill="none" />
                <path className="opacity-75" fill="currentColor" d="M4 12a8 8 0 018-8V0C5.373 0 0 5.373 0 12h4zm2 5.291A7.962 7.962 0 014 12H0c0 3.042 1.135 5.824 3 7.938l3-2.647z" />
              </svg>
              <span className="hidden sm:inline">Running:</span>
              <code className="bg-surface-800/80 px-2 py-0.5 rounded font-mono text-xs max-w-[200px] sm:max-w-none truncate">{lastCommand}</code>
              <span className="text-surface-400 hidden md:inline">(output in terminal)</span>
              <button
                onClick={async () => {
                  try {
                    const result = await api.cancelCommand();
                    if (result.cancelled) {
                      setExecutionStatus('failed');
                      setLastCommand(null);
                      setTimeout(() => setExecutionStatus('idle'), 3000);
                    }
                  } catch (e) {
                    console.error('Failed to cancel:', e);
                  }
                }}
                className="ml-2 sm:ml-4 px-2.5 sm:px-3 py-1 bg-red-500/20 hover:bg-red-500/30 text-red-300 border border-red-500/30 rounded-lg text-xs font-medium transition-colors"
              >
                Stop
              </button>
            </span>
          )}
          {executionStatus === 'success' && (
            <span className="flex items-center justify-center gap-2">
              <svg className="w-4 h-4" fill="none" stroke="currentColor" viewBox="0 0 24 24">
                <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M5 13l4 4L19 7" />
              </svg>
              Command completed successfully
            </span>
          )}
          {executionStatus === 'failed' && (
            <span className="flex items-center justify-center gap-2">
              <svg className="w-4 h-4" fill="none" stroke="currentColor" viewBox="0 0 24 24">
                <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M6 18L18 6M6 6l12 12" />
              </svg>
              <span className="hidden sm:inline">Command failed or cancelled - check terminal</span>
              <span className="sm:hidden">Command failed</span>
            </span>
          )}
        </div>
      )}

      {/* Main content - responsive padding and max-width */}
      <main className="max-w-7xl mx-auto px-4 sm:px-6 lg:px-8 py-4 sm:py-6 pb-20 sm:pb-24">
        {!serverConnected && (
          <div className="mb-4 sm:mb-6 p-3 sm:p-4 glass-light rounded-xl border border-yellow-500/20 animate-fade-in">
            <div className="flex items-start gap-3">
              <div className="w-8 h-8 rounded-lg bg-yellow-500/20 flex items-center justify-center flex-shrink-0">
                <svg className="w-4 h-4 text-yellow-400" fill="none" stroke="currentColor" viewBox="0 0 24 24">
                  <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M12 9v2m0 4h.01m-6.938 4h13.856c1.54 0 2.502-1.667 1.732-3L13.732 4c-.77-1.333-2.694-1.333-3.464 0L3.34 16c-.77 1.333.192 3 1.732 3z" />
                </svg>
              </div>
              <div>
                <p className="text-yellow-300 text-sm sm:text-base font-medium">Server not connected</p>
                <p className="text-yellow-200/70 text-xs sm:text-sm mt-1">
                  Run <code className="bg-surface-800/80 px-1.5 py-0.5 rounded font-mono text-yellow-300">pdd connect</code> in your terminal to enable command execution.
                </p>
              </div>
            </div>
          </div>
        )}

        {view === 'architecture' ? (
          <div className="animate-fade-in">
            <ArchitectureView
              serverConnected={serverConnected}
              isExecuting={isExecuting}
              onOpenPromptSpace={(prompt) => setEditingPrompt(prompt)}
              onBatchStart={handleBatchOperationStart}
              onBatchProgress={handleBatchOperationProgress}
              onBatchComplete={handleBatchOperationComplete}
            />
          </div>
        ) : view === 'prompts' ? (
          <div className="animate-fade-in">
            <div className="mb-4 sm:mb-6">
              <p className="text-surface-400 text-xs sm:text-sm">
                Select a prompt and click a command to run. Output appears in your terminal.
              </p>
            </div>
            <PromptSelector
              onSelectPrompt={setSelectedPrompt}
              onRunCommand={handleRunCommand}
              onEditPrompt={setEditingPrompt}
              onCreatePrompt={setEditingPrompt}
              onAddToQueue={handleOpenAddToQueueModal}
              selectedPrompt={selectedPrompt}
              isExecuting={isExecuting}
            />
          </div>
        ) : view === 'settings' ? (
          <div className="animate-fade-in">
            <ProjectSettings />
          </div>
        ) : (
          <div className="max-w-4xl mx-auto animate-fade-in">
            {/* Header */}
            <div className="mb-6 text-center sm:text-left">
              <h2 className="text-xl sm:text-2xl font-semibold text-white mb-2 flex items-center justify-center sm:justify-start gap-2">
                <span className="w-10 h-10 rounded-xl bg-red-500/20 flex items-center justify-center"><BugAntIcon className="w-5 h-5" /></span>
                Bug Investigation Agent
              </h2>
              <p className="text-surface-400 text-sm">
                Automatically investigate GitHub issues and generate failing test cases with AI-powered analysis.
              </p>
            </div>

            <div className="grid gap-4 lg:grid-cols-2">
              {/* Left column: Input and action */}
              <div className="space-y-4">
                {/* Main input card */}
                <div className="glass rounded-2xl p-4 sm:p-6 border border-surface-700/50">
                  <label className="block text-sm font-medium text-surface-300 mb-2">
                    GitHub Issue URL
                  </label>
                  <input
                    type="url"
                    value={bugIssueUrl}
                    onChange={(e) => setBugIssueUrl(e.target.value)}
                    placeholder="https://github.com/org/repo/issues/123"
                    className="w-full px-3 sm:px-4 py-2.5 sm:py-3 bg-surface-900/50 border border-surface-600 rounded-xl text-white placeholder-surface-500 focus:outline-none focus:border-accent-500 focus:ring-1 focus:ring-accent-500/50 transition-all text-sm sm:text-base"
                    disabled={isExecuting}
                  />

                  <button
                    onClick={handleRunBugCommand}
                    disabled={isExecuting || !serverConnected || !bugIssueUrl.trim()}
                    className={`
                      mt-4 w-full px-4 py-2.5 sm:py-3 rounded-xl font-medium transition-all duration-200 flex items-center justify-center gap-2 text-sm sm:text-base
                      ${isExecuting || !serverConnected || !bugIssueUrl.trim()
                        ? 'bg-surface-700 text-surface-500 cursor-not-allowed'
                        : 'bg-gradient-to-r from-red-600 to-red-500 hover:from-red-500 hover:to-red-400 text-white shadow-lg shadow-red-500/25 hover:shadow-red-500/40'}
                    `}
                  >
                    <BugAntIcon className="w-4 h-4" />
                    <span>Start Investigation</span>
                  </button>
                </div>

                {/* Prerequisites card */}
                <div className="glass rounded-2xl p-4 sm:p-5 border border-surface-700/50">
                  <h3 className="text-sm font-semibold text-white mb-3 flex items-center gap-2">
                    <svg className="w-4 h-4 text-yellow-400" fill="none" stroke="currentColor" viewBox="0 0 24 24">
                      <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M13 16h-1v-4h-1m1-4h.01M21 12a9 9 0 11-18 0 9 9 0 0118 0z" />
                    </svg>
                    Prerequisites
                  </h3>
                  <ul className="space-y-2 text-xs text-surface-400">
                    <li className="flex items-start gap-2">
                      <span className="w-4 h-4 rounded-full bg-surface-700 flex items-center justify-center text-[10px] text-surface-300 flex-shrink-0 mt-0.5">1</span>
                      <span><strong className="text-surface-300">GitHub CLI installed</strong> - Install from <code className="bg-surface-800 px-1 rounded text-accent-300">brew install gh</code> or <a href="https://cli.github.com" target="_blank" rel="noopener noreferrer" className="text-accent-400 hover:underline">cli.github.com</a></span>
                    </li>
                    <li className="flex items-start gap-2">
                      <span className="w-4 h-4 rounded-full bg-surface-700 flex items-center justify-center text-[10px] text-surface-300 flex-shrink-0 mt-0.5">2</span>
                      <span><strong className="text-surface-300">Authenticated with GitHub</strong> - Run <code className="bg-surface-800 px-1 rounded text-accent-300">gh auth login</code> if needed</span>
                    </li>
                    <li className="flex items-start gap-2">
                      <span className="w-4 h-4 rounded-full bg-surface-700 flex items-center justify-center text-[10px] text-surface-300 flex-shrink-0 mt-0.5">3</span>
                      <span><strong className="text-surface-300">Repository cloned locally</strong> - The agent works within your local codebase</span>
                    </li>
                  </ul>
                </div>

                {/* After investigation card */}
                <div className="glass rounded-2xl p-4 sm:p-5 border border-surface-700/50">
                  <h3 className="text-sm font-semibold text-white mb-3 flex items-center gap-2">
                    <svg className="w-4 h-4 text-green-400" fill="none" stroke="currentColor" viewBox="0 0 24 24">
                      <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M9 12l2 2 4-4m6 2a9 9 0 11-18 0 9 9 0 0118 0z" />
                    </svg>
                    After Investigation
                  </h3>
                  <ul className="space-y-2 text-xs text-surface-400">
                    <li className="flex items-start gap-2">
                      <span className="text-green-400">1.</span>
                      <span><strong className="text-surface-300">Review the draft PR</strong> - The agent creates a draft PR with a failing test</span>
                    </li>
                    <li className="flex items-start gap-2">
                      <span className="text-green-400">2.</span>
                      <span><strong className="text-surface-300">Fix the bug</strong> - Implement the fix to make the test pass</span>
                    </li>
                    <li className="flex items-start gap-2">
                      <span className="text-green-400">3.</span>
                      <span><strong className="text-surface-300">Mark PR ready</strong> - Convert from draft to ready for review</span>
                    </li>
                  </ul>
                </div>
              </div>

              {/* Right column: Workflow steps */}
              <div className="glass rounded-2xl p-4 sm:p-5 border border-surface-700/50">
                <h3 className="text-sm font-semibold text-white mb-4 flex items-center gap-2">
                  <svg className="w-4 h-4 text-accent-400" fill="none" stroke="currentColor" viewBox="0 0 24 24">
                    <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M13 10V3L4 14h7v7l9-11h-7z" />
                  </svg>
                  Agent Workflow (9 Steps)
                </h3>
                <div className="space-y-1">
                  {[
                    { step: 1, name: 'Duplicate Check', desc: 'Search for existing similar issues' },
                    { step: 2, name: 'Documentation Check', desc: 'Verify if it\'s a known issue or user error' },
                    { step: 3, name: 'Triage', desc: 'Assess if sufficient information is provided' },
                    { step: 4, name: 'Reproduce', desc: 'Attempt to reproduce the reported bug' },
                    { step: 5, name: 'Root Cause Analysis', desc: 'Identify the underlying cause' },
                    { step: 6, name: 'Test Plan', desc: 'Design a testing strategy' },
                    { step: 7, name: 'Generate Test', desc: 'Create a failing unit test' },
                    { step: 8, name: 'Verify Test', desc: 'Ensure test correctly detects the bug' },
                    { step: 9, name: 'Create PR', desc: 'Open a draft pull request' },
                  ].map((item) => (
                    <div key={item.step} className="flex items-start gap-3 py-1.5 px-2 rounded-lg hover:bg-surface-800/30 transition-colors">
                      <div className="w-5 h-5 rounded-full bg-surface-700 flex items-center justify-center text-[10px] font-medium text-surface-300 flex-shrink-0">
                        {item.step}
                      </div>
                      <div className="flex-1 min-w-0">
                        <div className="text-xs text-white font-medium">{item.name}</div>
                        <p className="text-[11px] text-surface-500">{item.desc}</p>
                      </div>
                    </div>
                  ))}
                </div>
                <div className="mt-4 pt-3 border-t border-surface-700/50">
                  <p className="text-xs text-surface-500">
                    <strong className="text-surface-400">Note:</strong> The agent may exit early if it detects a duplicate issue,
                    feature request, or insufficient information. Progress is shown in the terminal.
                  </p>
                </div>
              </div>
            </div>
          </div>
        )}
      </main>

      {/* Job Dashboard - shows active and completed jobs */}
      <JobDashboard
        activeJobs={activeJobs}
        completedJobs={completedJobs}
        selectedJob={selectedJob}
        onSelectJob={setSelectedJobId}
        onCancelJob={cancelJob}
        onRemoveJob={removeJob}
        onClearCompleted={clearCompletedJobs}
        onMarkSpawnedDone={markSpawnedJobDone}
        batchOperation={batchOperation}
        onCancelBatchOperation={handleCancelBatchOperation}
      />

      {/* Task Queue Panel - shows queued tasks for sequential execution */}
      <TaskQueuePanel
        tasks={taskQueue.tasks}
        executionMode={taskQueue.executionMode}
        isQueueRunning={taskQueue.isQueueRunning}
        isPaused={taskQueue.isPaused}
        progress={taskQueue.progress}
        onSetExecutionMode={taskQueue.setExecutionMode}
        onStartQueue={taskQueue.startQueue}
        onPauseQueue={taskQueue.pauseQueue}
        onResumeQueue={taskQueue.resumeQueue}
        onRunNextTask={taskQueue.runNextTask}
        onRemoveTask={taskQueue.removeTask}
        onSkipTask={taskQueue.skipTask}
        onRetryTask={taskQueue.retryTask}
        onReorderTasks={taskQueue.reorderTasks}
        onClearCompleted={taskQueue.clearCompleted}
        onClearAll={taskQueue.clearQueue}
      />

      {/* Add to Queue Modal */}
      <AddToQueueModal
        isOpen={showAddToQueueModal}
        prompt={addToQueuePrompt}
        onAddToQueue={handleAddToQueue}
        onClose={() => {
          setShowAddToQueueModal(false);
          setAddToQueuePrompt(null);
        }}
      />

      {/* Modern footer - responsive */}
      <footer className="fixed bottom-0 left-0 right-0 z-40 glass border-t border-surface-700/50 px-4 sm:px-6 py-2.5 sm:py-3">
        <div className="max-w-7xl mx-auto flex items-center justify-center gap-2 text-xs text-surface-500">
          <span className="w-4 h-4 rounded bg-surface-800/80 flex items-center justify-center p-0.5">
            <svg viewBox="0 0 1024 1024" className="w-full h-full" xmlns="http://www.w3.org/2000/svg">
              <g stroke="#00e3ff" strokeWidth="70" strokeLinecap="round" strokeLinejoin="round" fill="none">
                <path d="M 260 180 H 600 A 230 230 0 0 1 600 660 H 480 L 260 880 V 180 Z"/>
                <polyline points="505 340 585 420 505 500"/>
              </g>
            </svg>
          </span>
          <span className="hidden sm:inline">Prompt Driven Development</span>
          <span className="sm:hidden">PDD</span>
          <span className="text-surface-600">•</span>
          <span>{isAnyJobRunning ? 'Jobs running - see dashboard below' : 'Commands tracked in dashboard'}</span>
        </div>
      </footer>

      {/* Re-authentication modal */}
      {showReauthModal && (
        <ReauthModal onClose={() => setShowReauthModal(false)} />
      )}
    </div>
    </ErrorBoundary>
  );
};

export default App;
