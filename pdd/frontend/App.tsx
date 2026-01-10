import React, { useState, useEffect } from 'react';
import { CommandType } from './types';
import { COMMANDS } from './constants';
import PromptSelector from './components/PromptSelector';
import PromptSpace from './components/PromptSpace';
import ArchitectureView from './components/ArchitectureView';
import ProjectSettings from './components/ProjectSettings';
import { api, PromptInfo, RunResult } from './api';
import { Squares2X2Icon, DocumentTextIcon, BugAntIcon, Cog6ToothIcon } from './components/Icon';

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
    setLastCommand(`pdd ${config.backendName} ${displayArg}${optionsStr}`);

    try {
      // Build the command request based on command type
      const args: Record<string, any> = {};

      // For sync command, use sync_basename (without language suffix)
      // e.g., "calculator" not "calculator_python"
      if (command === CommandType.SYNC) {
        args.basename = prompt.sync_basename;
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
      }

      const result = await api.runCommand({
        command: config.backendName,
        args,
        options,
      });

      setLastRunResult(result);
      setExecutionStatus(result.success ? 'success' : 'failed');

      // Reset status after 5 seconds (keep error details visible longer)
      setTimeout(() => {
        setExecutionStatus('idle');
        setLastCommand(null);
        if (result.success) setLastRunResult(null);
      }, result.success ? 5000 : 10000);
    } catch (error: any) {
      console.error('Failed to execute command:', error);
      setLastRunResult({
        success: false,
        message: error.message || 'Failed to execute command',
        exit_code: 1,
        error_details: error.message,
      });
      setExecutionStatus('failed');
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
    setLastCommand(`pdd bug ${bugIssueUrl}`);

    try {
      // Bug command expects 'args' as tuple with the URL
      const result = await api.runCommand({
        command: 'bug',
        args: { args: [bugIssueUrl] },
        options: {},
      });

      setExecutionStatus(result.success ? 'success' : 'failed');
      setTimeout(() => {
        setExecutionStatus('idle');
        setLastCommand(null);
      }, 5000);
    } catch (error: any) {
      console.error('Failed to execute bug command:', error);
      setExecutionStatus('failed');
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
              selectedPrompt={selectedPrompt}
              isExecuting={isExecuting}
            />
          </div>
        ) : view === 'settings' ? (
          <div className="animate-fade-in">
            <ProjectSettings />
          </div>
        ) : (
          <div className="max-w-2xl mx-auto animate-fade-in">
            <div className="mb-4 sm:mb-6 text-center sm:text-left">
              <h2 className="text-xl sm:text-2xl font-semibold text-white mb-2 flex items-center justify-center sm:justify-start gap-2">
                <span className="w-10 h-10 rounded-xl bg-red-500/20 flex items-center justify-center"><BugAntIcon className="w-5 h-5" /></span>
                Bug Investigation
              </h2>
              <p className="text-surface-400 text-sm">
                Enter a GitHub issue URL to investigate a bug using AI-powered analysis.
              </p>
            </div>

            <div className="glass rounded-2xl p-4 sm:p-6 border border-surface-700/50 card-hover">
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
              <p className="mt-2 text-xs text-surface-500">
                The AI will analyze the issue, understand the codebase, and generate a reproducing test case.
              </p>

              <button
                onClick={handleRunBugCommand}
                disabled={isExecuting || !serverConnected || !bugIssueUrl.trim()}
                className={`
                  mt-4 w-full px-4 py-2.5 sm:py-3 rounded-xl font-medium transition-all duration-200 flex items-center justify-center gap-2 text-sm sm:text-base
                  ${isExecuting || !serverConnected || !bugIssueUrl.trim()
                    ? 'bg-surface-700 text-surface-500 cursor-not-allowed'
                    : 'bg-gradient-to-r from-accent-600 to-accent-500 hover:from-accent-500 hover:to-accent-400 text-white shadow-lg shadow-accent-500/25 hover:shadow-accent-500/40'}
                `}
              >
                <BugAntIcon className="w-4 h-4" />
                <span>Investigate Bug</span>
              </button>
            </div>
          </div>
        )}
      </main>

      {/* Modern footer - responsive */}
      <footer className="fixed bottom-0 left-0 right-0 glass border-t border-surface-700/50 px-4 sm:px-6 py-2.5 sm:py-3">
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
          <span>Commands run in your terminal</span>
        </div>
      </footer>
    </div>
  );
};

export default App;
