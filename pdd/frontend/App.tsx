import React, { useState, useEffect, useCallback, useRef } from 'react';
import { CommandType } from './types';
import { COMMANDS } from './constants';
import { buildCommandRequest, buildDisplayCommand } from './lib/commandBuilder';
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
import RemoteSessionSelector from './components/RemoteSessionSelector';
import ExecutionModeToggle from './components/ExecutionModeToggle';
import DeviceIndicator from './components/DeviceIndicator';
import { api, PromptInfo, RunResult, CommandRequest, RemoteSessionInfo } from './api';
import { Squares2X2Icon, DocumentTextIcon, BugAntIcon, Cog6ToothIcon } from './components/Icon';
import { useJobs, JobInfo } from './hooks/useJobs';
import { useTaskQueue, TaskQueueItem } from './hooks/useTaskQueue';
import { useToast } from './components/Toast';
import { useAudioNotification } from './hooks/useAudioNotification';

type View = 'devunits' | 'bug' | 'fix' | 'change' | 'settings';
type DevUnitsSubView = 'graph' | 'list';

// Parse URL hash to get initial view and prompt path
const parseHash = (): { view: View; promptPath?: string; subView?: DevUnitsSubView } => {
  const hash = window.location.hash.slice(1); // Remove #
  if (!hash) return { view: 'devunits', subView: 'graph' };

  const [viewPart, ...promptParts] = hash.split('/');
  const promptPath = promptParts.length > 0 ? promptParts.join('/') : undefined;

  // Map legacy views to new structure
  if (viewPart === 'architecture') return { view: 'devunits', subView: 'graph', promptPath };
  if (viewPart === 'prompts') return { view: 'devunits', subView: 'list', promptPath };

  const validViews: View[] = ['devunits', 'bug', 'fix', 'change', 'settings'];
  const view = validViews.includes(viewPart as View) ? (viewPart as View) : 'devunits';

  return { view, promptPath, subView: view === 'devunits' ? 'graph' : undefined };
};

const App: React.FC = () => {
  const initialState = parseHash();
  const [view, setView] = useState<View>(initialState.view);
  const [devUnitsSubView, setDevUnitsSubView] = useState<DevUnitsSubView>(initialState.subView || 'graph');
  const [pendingPromptPath, setPendingPromptPath] = useState<string | undefined>(initialState.promptPath);
  const [selectedPrompt, setSelectedPrompt] = useState<PromptInfo | null>(null);
  const [editingPrompt, setEditingPrompt] = useState<PromptInfo | null>(null);
  const [isExecuting, setIsExecuting] = useState(false);
  const [executionStatus, setExecutionStatus] = useState<'idle' | 'running' | 'success' | 'failed'>('idle');
  const [lastCommand, setLastCommand] = useState<string | null>(null);
  const [lastRunResult, setLastRunResult] = useState<RunResult | null>(null);
  const [serverConnected, setServerConnected] = useState(false);

  // Counter to trigger ArchitectureView prompt refresh after sync completions
  const [syncCompletedCounter, setSyncCompletedCounter] = useState(0);

  // Bug command state
  const [bugIssueUrl, setBugIssueUrl] = useState('');

  // Fix command state
  const [fixPrUrl, setFixPrUrl] = useState('');

  // Change command state
  const [changeIssueUrl, setChangeIssueUrl] = useState('');

  // Batch operation state (for architecture prompt generation)
  const [batchOperation, setBatchOperation] = useState<BatchOperation | null>(null);

  // Auth modal state
  const [showReauthModal, setShowReauthModal] = useState(false);

  // Add to queue modal state
  const [showAddToQueueModal, setShowAddToQueueModal] = useState(false);
  const [addToQueuePrompt, setAddToQueuePrompt] = useState<PromptInfo | null>(null);

  // Toast notifications
  const { addToast } = useToast();

  // Audio notifications for job completion
  const { audioEnabled, setAudioEnabled, playNotification, testSound } = useAudioNotification();

  // Toggle audio with confirmation sound
  const handleToggleAudio = useCallback(() => {
    const newEnabled = !audioEnabled;
    setAudioEnabled(newEnabled);
    if (newEnabled) {
      // Play test sound when enabling to confirm it works
      testSound(true);
    }
  }, [audioEnabled, setAudioEnabled, testSound]);

  // Remote session state
  const [executionMode, setExecutionMode] = useState<'local' | 'remote'>('remote');
  const [remoteSessions, setRemoteSessions] = useState<RemoteSessionInfo[]>([]);
  const [selectedRemoteSession, setSelectedRemoteSession] = useState<string | null>(null);
  const [remoteSessionError, setRemoteSessionError] = useState<string | null>(null);
  const [showRemotePanel, setShowRemotePanel] = useState(false);

  // Jobs dashboard visibility state
  const [showJobsDashboard, setShowJobsDashboard] = useState(false);

  // Track scroll position and sub-view when entering PromptSpace to restore on back
  // Using refs to persist across the component unmount/remount cycle
  const savedScrollPositionRef = useRef<number>(0);
  const savedSubViewRef = useRef<DevUnitsSubView>(devUnitsSubView);

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
      playNotification(success);
      if (success && task.commandType === CommandType.SYNC) {
        setSyncCompletedCounter(prev => prev + 1);
      }
    },
    onQueueComplete: () => {
      addToast('Task queue completed', 'success', 3000);
      playNotification(true);
    },
  });

  // Job management for multi-session support
  const handleJobComplete = useCallback((job: JobInfo, success: boolean) => {
    addToast(
      `${job.displayCommand} ${success ? 'completed successfully' : 'failed'}`,
      success ? 'success' : 'error',
      5000
    );
    // Play audio notification
    playNotification(success);
    // Notify task queue if this job was part of the queue
    taskQueue.handleJobComplete(job.id, success);
    // Refresh architecture view prompt info after sync completes
    if (success && job.command === 'sync') {
      setSyncCompletedCounter(prev => prev + 1);
    }
  }, [addToast, playNotification, taskQueue]);

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
    markJobStatus,
    updateSpawnedJobStatus,
  } = useJobs({ onJobComplete: handleJobComplete });

  // Create a job runner for the task queue that respects execution mode
  // Rebuilds the command from raw inputs to match handleRunCommand behavior exactly
  const executeQueuedTask = useCallback(async (
    task: TaskQueueItem
  ): Promise<string | null> => {
    try {
      // Rebuild the command using the same centralized builder as handleRunCommand
      // This ensures queue execution uses identical logic to direct execution
      const { args, options, displayCommand, backendName } = buildCommandRequest(
        task.commandType,
        task.prompt,
        task.rawOptions
      );

      // Check if we're in remote mode with a selected session
      if (executionMode === 'remote' && selectedRemoteSession) {
        // Submit to remote session via cloud
        const { commandId } = await api.submitRemoteCommand({
          sessionId: selectedRemoteSession,
          type: backendName,
          payload: { args, options },
        });
        // Add to job dashboard as remote job
        addSpawnedJob(
          `[Remote] ${displayCommand}`,
          backendName,
          commandId,
          { remote: true, sessionId: selectedRemoteSession }
        );
        return commandId;
      } else {
        // Local execution - spawn in new terminal window
        const result = await api.spawnTerminal({
          command: backendName,
          args,
          options,
        });
        if (result.success && result.job_id) {
          // Add to job dashboard for tracking
          addSpawnedJob(displayCommand, backendName, result.job_id);
          return result.job_id;
        } else {
          console.error('Failed to spawn terminal:', result.message);
          return null;
        }
      }
    } catch (error) {
      console.error('Failed to submit job:', error);
      return null;
    }
  }, [addSpawnedJob, executionMode, selectedRemoteSession]);

  // Connect the task queue job runner
  useEffect(() => {
    taskQueue.setSubmitJob(executeQueuedTask);
  }, [taskQueue, executeQueuedTask]);

  // Handler to add task to queue
  // Now stores raw inputs (commandType, prompt, rawOptions) for reconstruction at execution time
  const handleAddToQueue = useCallback((
    commandType: CommandType,
    prompt: PromptInfo,
    rawOptions: Record<string, any>,
    displayCommand: string
  ) => {
    taskQueue.addTask(commandType, prompt, rawOptions, displayCommand);
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
    } else if (view === 'devunits') {
      window.location.hash = devUnitsSubView === 'graph' ? 'architecture' : 'prompts';
    } else {
      window.location.hash = view;
    }
  }, [view, editingPrompt, devUnitsSubView]);

  // Handle browser back/forward navigation
  useEffect(() => {
    const handleHashChange = () => {
      const { view: newView, promptPath, subView } = parseHash();
      setView(newView);
      if (subView) setDevUnitsSubView(subView);
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

  // Fetch remote sessions on mount and refresh every 30 seconds
  useEffect(() => {
    if (!serverConnected) return;

    const fetchRemoteSessions = async () => {
      try {
        const sessions = await api.listRemoteSessions();
        setRemoteSessions(sessions);
        setRemoteSessionError(null); // Clear any previous errors
        // Auto-select first available session if none is selected
        if (sessions.length > 0) {
          setSelectedRemoteSession(prev => prev || sessions[0].sessionId);
        }
      } catch (err) {
        const errorMsg = err instanceof Error ? err.message : String(err);
        console.error('Failed to fetch remote sessions:', errorMsg);
        setRemoteSessionError(errorMsg);

        // Parse error type and show appropriate toast
        if (errorMsg.includes('Not authenticated') || errorMsg.includes('401') || errorMsg.includes('403')) {
          // Don't spam toast for auth errors - user might not be logged in yet
          // Error will be shown in debug panel
        } else if (errorMsg.includes('timeout') || errorMsg.includes('network') || errorMsg.includes('Failed to fetch')) {
          addToast('Network error: Cannot reach cloud. Check your connection.', 'error', 5000);
        } else {
          addToast(`Failed to load remote sessions: ${errorMsg}`, 'error', 5000);
        }
      }
    };

    // Initial fetch
    fetchRemoteSessions();

    // Refresh every 30s
    const interval = setInterval(fetchRemoteSessions, 30000);

    return () => clearInterval(interval);
  }, [serverConnected, addToast]);


  const handleRunCommand = async (command: CommandType, prompt: PromptInfo, commandOptions?: Record<string, any>) => {
    if (!serverConnected) {
      alert('Server not connected. Run "pdd connect" in your terminal first.');
      return;
    }

    const config = COMMANDS[command];
    setIsExecuting(true);
    setExecutionStatus('running');

    // Use centralized command builder for consistent argument handling
    const { args, options, displayCommand: fullDisplayCommand } = buildCommandRequest(
      command,
      prompt,
      commandOptions || {}
    );
    setLastCommand(fullDisplayCommand);

    try {

      // Check if we're in remote mode
      if (executionMode === 'remote' && selectedRemoteSession) {
        // Validate session is not stale before submitting
        const selectedSession = remoteSessions.find(s => s.sessionId === selectedRemoteSession);
        if (selectedSession?.status === 'stale') {
          const shouldContinue = window.confirm(
            'Warning: The selected session appears to be offline (stale).\n\n' +
            'The remote machine may not be running or has lost connection.\n' +
            'The command may not be executed.\n\n' +
            'Do you want to submit anyway?'
          );
          if (!shouldContinue) {
            setIsExecuting(false);
            setExecutionStatus('idle');
            return;
          }
        }

        // Submit command to remote session via cloud
        try {
          const { commandId } = await api.submitRemoteCommand({
            sessionId: selectedRemoteSession,
            type: config.backendName,
            payload: { args, options },
          });

          // Add to job dashboard as a remote job
          // useJobs.ts will automatically poll for status updates on remote jobs
          addSpawnedJob(
            `[Remote] ${fullDisplayCommand}`,
            config.backendName,
            commandId,
            { remote: true, sessionId: selectedRemoteSession }
          );

          setExecutionStatus('success');
          addToast(`Command submitted to remote session`, 'success', 3000);
        } catch (error) {
          setExecutionStatus('failed');
          addToast(
            `Failed to submit remote command: ${error instanceof Error ? error.message : String(error)}`,
            'error',
            5000
          );
        }
      } else {
        // Local execution: Spawn command in a new terminal window for complete isolation
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
      // Check if we're in remote mode
      if (executionMode === 'remote' && selectedRemoteSession) {
        // Validate session is not stale before submitting
        const selectedSession = remoteSessions.find(s => s.sessionId === selectedRemoteSession);
        if (selectedSession?.status === 'stale') {
          const shouldContinue = window.confirm(
            'Warning: The selected session appears to be offline (stale).\n\n' +
            'The remote machine may not be running or has lost connection.\n' +
            'The command may not be executed.\n\n' +
            'Do you want to submit anyway?'
          );
          if (!shouldContinue) {
            setIsExecuting(false);
            setExecutionStatus('idle');
            return;
          }
        }

        // Submit command to remote session via cloud
        try {
          const { commandId } = await api.submitRemoteCommand({
            sessionId: selectedRemoteSession,
            type: 'bug',
            payload: { args: { args: [bugIssueUrl] }, options: {} },
          });

          // Add to job dashboard as a remote job
          addSpawnedJob(
            `[Remote] ${displayCommand}`,
            'bug',
            commandId,
            { remote: true, sessionId: selectedRemoteSession }
          );

          setExecutionStatus('success');
          addToast(`Command submitted to remote session`, 'success', 3000);
        } catch (error) {
          setExecutionStatus('failed');
          addToast(
            `Failed to submit remote command: ${error instanceof Error ? error.message : String(error)}`,
            'error',
            5000
          );
        }
      } else {
        // Local execution: Spawn bug command in a new terminal window for complete isolation
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

  const handleRunFixCommand = async () => {
    if (!serverConnected) {
      alert('Server not connected. Run "pdd connect" in your terminal first.');
      return;
    }

    if (!fixPrUrl.trim()) {
      alert('Please enter a GitHub PR URL');
      return;
    }

    setIsExecuting(true);
    setExecutionStatus('running');
    const displayCommand = `pdd fix ${fixPrUrl}`;
    setLastCommand(displayCommand);

    try {
      // Check if we're in remote mode
      if (executionMode === 'remote' && selectedRemoteSession) {
        // Validate session is not stale before submitting
        const selectedSession = remoteSessions.find(s => s.sessionId === selectedRemoteSession);
        if (selectedSession?.status === 'stale') {
          const shouldContinue = window.confirm(
            'Warning: The selected session appears to be offline (stale).\n\n' +
            'The remote machine may not be running or has lost connection.\n' +
            'The command may not be executed.\n\n' +
            'Do you want to submit anyway?'
          );
          if (!shouldContinue) {
            setIsExecuting(false);
            setExecutionStatus('idle');
            return;
          }
        }

        // Submit command to remote session via cloud
        try {
          const { commandId } = await api.submitRemoteCommand({
            sessionId: selectedRemoteSession,
            type: 'fix',
            payload: { args: { args: [fixPrUrl] }, options: {} },
          });

          // Add to job dashboard as a remote job
          addSpawnedJob(
            `[Remote] ${displayCommand}`,
            'fix',
            commandId,
            { remote: true, sessionId: selectedRemoteSession }
          );

          setExecutionStatus('success');
          addToast(`Command submitted to remote session`, 'success', 3000);
        } catch (error) {
          setExecutionStatus('failed');
          addToast(
            `Failed to submit remote command: ${error instanceof Error ? error.message : String(error)}`,
            'error',
            5000
          );
        }
      } else {
        // Local execution: Spawn fix command in a new terminal window
        const result = await api.spawnTerminal({
          command: 'fix',
          args: { args: [fixPrUrl] },
          options: {},
        });

        if (result.success) {
          // Add to job dashboard for tracking with server-provided job_id
          addSpawnedJob(displayCommand, 'fix', result.job_id);
          setExecutionStatus('success');
          addToast(`Opened terminal: ${displayCommand}`, 'success', 3000);
        } else {
          setExecutionStatus('failed');
          addToast(`Failed to open terminal: ${result.message}`, 'error', 5000);
        }
      }

      setTimeout(() => {
        setExecutionStatus('idle');
        setLastCommand(null);
      }, 3000);
    } catch (error: any) {
      console.error('Failed to execute fix command:', error);
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

  const handleRunChangeCommand = async () => {
    if (!serverConnected) {
      alert('Server not connected. Run "pdd connect" in your terminal first.');
      return;
    }

    if (!changeIssueUrl.trim()) {
      alert('Please enter a GitHub issue URL');
      return;
    }

    setIsExecuting(true);
    setExecutionStatus('running');
    const displayCommand = `pdd change ${changeIssueUrl}`;
    setLastCommand(displayCommand);

    try {
      // Check if we're in remote mode
      if (executionMode === 'remote' && selectedRemoteSession) {
        // Validate session is not stale before submitting
        const selectedSession = remoteSessions.find(s => s.sessionId === selectedRemoteSession);
        if (selectedSession?.status === 'stale') {
          const shouldContinue = window.confirm(
            'Warning: The selected session appears to be offline (stale).\n\n' +
            'The remote machine may not be running or has lost connection.\n' +
            'The command may not be executed.\n\n' +
            'Do you want to submit anyway?'
          );
          if (!shouldContinue) {
            setIsExecuting(false);
            setExecutionStatus('idle');
            return;
          }
        }

        // Submit command to remote session via cloud
        try {
          const { commandId } = await api.submitRemoteCommand({
            sessionId: selectedRemoteSession,
            type: 'change',
            payload: { args: { args: [changeIssueUrl] }, options: {} },
          });

          // Add to job dashboard as a remote job
          addSpawnedJob(
            `[Remote] ${displayCommand}`,
            'change',
            commandId,
            { remote: true, sessionId: selectedRemoteSession }
          );

          setExecutionStatus('success');
          addToast(`Command submitted to remote session`, 'success', 3000);
        } catch (error) {
          setExecutionStatus('failed');
          addToast(
            `Failed to submit remote command: ${error instanceof Error ? error.message : String(error)}`,
            'error',
            5000
          );
        }
      } else {
        // Local execution: Spawn change command in a new terminal window
        const result = await api.spawnTerminal({
          command: 'change',
          args: { args: [changeIssueUrl] },
          options: {},
        });

        if (result.success) {
          // Add to job dashboard for tracking with server-provided job_id
          addSpawnedJob(displayCommand, 'change', result.job_id);
          setExecutionStatus('success');
          addToast(`Opened terminal: ${displayCommand}`, 'success', 3000);
        } else {
          setExecutionStatus('failed');
          addToast(`Failed to open terminal: ${result.message}`, 'error', 5000);
        }
      }

      setTimeout(() => {
        setExecutionStatus('idle');
        setLastCommand(null);
      }, 3000);
    } catch (error: any) {
      console.error('Failed to execute change command:', error);
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

  // Handler for PromptSpace add to queue
  const handlePromptSpaceAddToQueue = (command: CommandType, options?: Record<string, any>) => {
    if (editingPrompt) {
      const rawOptions = options || {};
      const displayCommand = buildDisplayCommand(command, editingPrompt, rawOptions);
      handleAddToQueue(command, editingPrompt, rawOptions, displayCommand);
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

  // Open prompt space and save scroll position + sub-view for back navigation
  const handleOpenPromptSpace = useCallback((prompt: PromptInfo) => {
    savedScrollPositionRef.current = window.scrollY;
    savedSubViewRef.current = devUnitsSubView;
    setEditingPrompt(prompt);
  }, [devUnitsSubView]);

  // Handle back from PromptSpace - restore sub-view and scroll position
  const handleBackFromPromptSpace = useCallback(() => {
    const scrollY = savedScrollPositionRef.current;
    const previousSubView = savedSubViewRef.current;

    // Restore the sub-view first
    setDevUnitsSubView(previousSubView);
    setEditingPrompt(null);

    // Restore scroll position after React fully re-renders the previous view
    // Use multiple attempts to ensure DOM is ready
    const restoreScroll = () => {
      window.scrollTo({ top: scrollY, behavior: 'instant' });
    };
    // Try immediately, then after short delays to catch async renders
    setTimeout(restoreScroll, 0);
    setTimeout(restoreScroll, 100);
    setTimeout(restoreScroll, 250);
  }, []);

  return (
    <ErrorBoundary>
    <div className="min-h-screen bg-surface-950">
      {/* Modern responsive header - Restructured with branding left, workflows center, status right */}
      <header className="glass sticky top-0 z-40 border-b border-surface-700/50">
        <div className="mx-auto px-4 sm:px-6 lg:px-8 2xl:px-12">
          <div className="flex items-center justify-between h-16 gap-4">
            {/* LEFT: Branding */}
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
                <h1 className="text-base sm:text-lg font-bold text-white whitespace-nowrap">Prompt Driven</h1>
              </div>
            </div>

            {/* CENTER: Main workflow buttons with gold border */}
            <div className="flex-1 flex justify-center">
              <div className="flex gap-1 sm:gap-1.5 p-1.5 rounded-xl border-2 border-[#FDCE49]/60 bg-surface-800/40 max-w-fit overflow-x-auto scrollbar-hide">
                <button
                  onClick={() => setView('devunits')}
                  className={`px-3 sm:px-4 py-1.5 sm:py-2 rounded-lg text-xs sm:text-sm font-medium transition-all duration-200 ${
                    view === 'devunits'
                      ? 'bg-[#DFA84A] text-surface-900 shadow-lg'
                      : 'text-surface-300 hover:text-white hover:bg-surface-700/80 hover:shadow-[0_0_10px_rgba(253,206,73,0.3)]'
                  }`}
                >
                  <Squares2X2Icon className="hidden sm:inline w-4 h-4 mr-1.5" />Dev Units
                </button>
                <button
                  onClick={() => setView('bug')}
                  className={`px-3 sm:px-4 py-1.5 sm:py-2 rounded-lg text-xs sm:text-sm font-medium transition-all duration-200 ${
                    view === 'bug'
                      ? 'bg-[#DFA84A] text-surface-900 shadow-lg'
                      : 'text-surface-300 hover:text-white hover:bg-surface-700/80 hover:shadow-[0_0_10px_rgba(253,206,73,0.3)]'
                  }`}
                >
                  <BugAntIcon className="hidden sm:inline w-4 h-4 mr-1.5" />Bug
                </button>
                <button
                  onClick={() => setView('fix')}
                  className={`px-3 sm:px-4 py-1.5 sm:py-2 rounded-lg text-xs sm:text-sm font-medium transition-all duration-200 ${
                    view === 'fix'
                      ? 'bg-[#DFA84A] text-surface-900 shadow-lg'
                      : 'text-surface-300 hover:text-white hover:bg-surface-700/80 hover:shadow-[0_0_10px_rgba(253,206,73,0.3)]'
                  }`}
                >
                  <svg className="hidden sm:inline w-4 h-4 mr-1.5" fill="none" stroke="currentColor" viewBox="0 0 24 24">
                    <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M11 5H6a2 2 0 00-2 2v11a2 2 0 002 2h11a2 2 0 002-2v-5m-1.414-9.414a2 2 0 112.828 2.828L11.828 15H9v-2.828l8.586-8.586z" />
                  </svg>Fix
                </button>
                <button
                  onClick={() => setView('change')}
                  className={`px-3 sm:px-4 py-1.5 sm:py-2 rounded-lg text-xs sm:text-sm font-medium transition-all duration-200 ${
                    view === 'change'
                      ? 'bg-[#DFA84A] text-surface-900 shadow-lg'
                      : 'text-surface-300 hover:text-white hover:bg-surface-700/80 hover:shadow-[0_0_10px_rgba(253,206,73,0.3)]'
                  }`}
                >
                  <svg className="hidden sm:inline w-4 h-4 mr-1.5" fill="none" stroke="currentColor" viewBox="0 0 24 24">
                    <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M12 6V4m0 2a2 2 0 100 4m0-4a2 2 0 110 4m-6 8a2 2 0 100-4m0 4a2 2 0 110-4m0 4v2m0-6V4m6 6v10m6-2a2 2 0 100-4m0 4a2 2 0 110-4m0 4v2m0-6V4" />
                  </svg>Change
                </button>
                <button
                  onClick={() => setView('settings')}
                  className={`px-3 sm:px-4 py-1.5 sm:py-2 rounded-lg text-xs sm:text-sm font-medium transition-all duration-200 ${
                    view === 'settings'
                      ? 'bg-[#DFA84A] text-surface-900 shadow-lg'
                      : 'text-surface-300 hover:text-white hover:bg-surface-700/80 hover:shadow-[0_0_10px_rgba(253,206,73,0.3)]'
                  }`}
                >
                  <Cog6ToothIcon className="hidden sm:inline w-4 h-4 mr-1.5" />Settings
                </button>
              </div>
            </div>

            {/* RIGHT: Live status section */}
            <div className="flex items-center gap-2 sm:gap-3 flex-shrink-0">
              {/* Jobs button with LED indicator - toggles dashboard visibility */}
              <button
                onClick={() => setShowJobsDashboard(!showJobsDashboard)}
                className={`relative flex items-center gap-2 px-2 sm:px-3 py-1.5 rounded-lg text-xs sm:text-sm font-medium transition-all ${
                  showJobsDashboard
                    ? 'bg-surface-700 text-white'
                    : 'bg-surface-700/50 text-surface-300 border border-surface-600/50 hover:bg-surface-700'
                }`}
                title={activeJobs.length > 0 ? `${activeJobs.length} jobs running - click to ${showJobsDashboard ? 'hide' : 'show'}` : 'Show jobs dashboard'}
              >
                {/* LED indicator */}
                <span className={`w-2.5 h-2.5 rounded-full ${
                  activeJobs.length > 0
                    ? 'bg-green-400 shadow-[0_0_8px_rgba(74,222,128,0.8)] animate-pulse'
                    : 'bg-green-900/50 border border-green-800/50'
                }`} />
                <span className="hidden sm:inline">Jobs</span>
                {activeJobs.length > 0 && (
                  <span className="text-green-400 font-mono text-xs">
                    {activeJobs.length}
                  </span>
                )}
              </button>

              {/* Remote/Local toggle */}
              <button
                onClick={() => setShowRemotePanel(!showRemotePanel)}
                className={`flex items-center gap-1.5 px-2 sm:px-3 py-1.5 rounded-lg text-xs sm:text-sm font-medium transition-colors ${
                  executionMode === 'remote'
                    ? 'bg-blue-500/20 text-blue-400 border border-blue-500/30'
                    : 'bg-surface-700/50 text-surface-400 border border-surface-600/50 hover:bg-surface-700'
                }`}
                title={showRemotePanel ? 'Hide remote session panel' : 'Show remote session panel'}
              >
                <span aria-hidden="true">{executionMode === 'remote' ? '🌐' : '💻'}</span>
                <span className="sr-only">
                  {executionMode === 'remote' ? 'Remote execution mode' : 'Local execution mode'}
                </span>
                <span className="hidden sm:inline">{executionMode === 'remote' ? 'Remote' : 'Local'}</span>
              </button>

              {/* Connection status */}
              <div className={`flex items-center gap-1.5 text-xs px-2 py-1.5 rounded-full transition-colors ${
                serverConnected
                  ? 'bg-green-500/10 text-green-400 border border-green-500/20'
                  : 'bg-yellow-500/10 text-yellow-400 border border-yellow-500/20'
              }`}>
                <span className={`w-2 h-2 rounded-full ${serverConnected ? 'bg-green-400 animate-pulse-slow' : 'bg-yellow-400 animate-pulse'}`} />
                <span className="hidden sm:inline">{serverConnected ? 'Connected' : 'Offline'}</span>
              </div>

              {/* Audio toggle */}
              <button
                onClick={handleToggleAudio}
                className={`p-1.5 rounded-lg transition-colors ${
                  audioEnabled
                    ? 'text-accent-400 hover:bg-accent-500/20'
                    : 'text-surface-500 hover:bg-surface-700/50'
                }`}
                title={audioEnabled ? 'Sound notifications on' : 'Sound notifications off'}
              >
                <svg className="w-4 h-4" fill="none" stroke="currentColor" viewBox="0 0 24 24">
                  {audioEnabled ? (
                    <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M15.536 8.464a5 5 0 010 7.072m2.828-9.9a9 9 0 010 12.728M5.586 15H4a1 1 0 01-1-1v-4a1 1 0 011-1h1.586l4.707-4.707C10.923 3.663 12 4.109 12 5v14c0 .891-1.077 1.337-1.707.707L5.586 15z" />
                  ) : (
                    <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M5.586 15H4a1 1 0 01-1-1v-4a1 1 0 011-1h1.586l4.707-4.707C10.923 3.663 12 4.109 12 5v14c0 .891-1.077 1.337-1.707.707L5.586 15zm11.707-6.707l4 4m0-4l-4 4" />
                  )}
                </svg>
              </button>

              {/* Cloud auth status */}
              <AuthStatusIndicator onReauth={() => setShowReauthModal(true)} />
            </div>
          </div>
        </div>
      </header>

      {/* Remote/Local Dropdown Modal - positioned relative to the header */}
      {showRemotePanel && (
        <>
          {/* Backdrop for click-outside dismiss */}
          <div
            className="fixed inset-0 z-30"
            onClick={() => setShowRemotePanel(false)}
          />
          {/* Dropdown modal - max 1/3 width, positioned in top-right area */}
          <div className="absolute top-16 right-4 sm:right-6 lg:right-8 z-40 w-[min(90vw,400px)] max-w-[33vw] min-w-[280px] animate-slide-down">
            <div className="glass rounded-xl border border-surface-700/50 shadow-2xl overflow-hidden">
              {/* Header */}
              <div className="px-4 py-3 border-b border-surface-700/50 bg-surface-800/50">
                <h3 className="text-sm font-medium text-white">Execution Settings</h3>
              </div>

              <div className="p-4 space-y-4">
                {/* Execution mode toggle */}
                <div>
                  <ExecutionModeToggle
                    mode={executionMode}
                    onModeChange={setExecutionMode}
                  />
                </div>

                {/* Remote session selector - only shown in remote mode */}
                {executionMode === 'remote' && (
                  <div>
                    <RemoteSessionSelector
                      sessions={remoteSessions}
                      selectedSessionId={selectedRemoteSession}
                      onSelectSession={setSelectedRemoteSession}
                      error={remoteSessionError}
                      onRefresh={async () => {
                        try {
                          const sessions = await api.listRemoteSessions();
                          setRemoteSessions(sessions);
                          setRemoteSessionError(null);
                        } catch (err) {
                          setRemoteSessionError(err instanceof Error ? err.message : String(err));
                        }
                      }}
                    />
                  </div>
                )}

                {/* Help text */}
                <p className="text-xs text-surface-500">
                  {executionMode === 'local'
                    ? 'Commands execute on this machine in terminal windows.'
                    : selectedRemoteSession
                      ? 'Commands will be sent to the selected remote session via cloud.'
                      : 'Select a remote session to execute commands remotely.'}
                </p>
              </div>

              {/* Footer with Done button */}
              <div className="px-4 py-3 border-t border-surface-700/50 bg-surface-800/30">
                <button
                  onClick={() => setShowRemotePanel(false)}
                  className="w-full px-4 py-2 bg-[#DFA84A] hover:bg-[#FDCE49] text-surface-900 rounded-lg text-sm font-medium transition-colors"
                >
                  Done
                </button>
              </div>
            </div>
          </div>
        </>
      )}

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

      {/* Sub-navigation area - full width, just below nav bar */}
      <div className="glass border-b border-surface-700/50">
        <div className="mx-auto px-4 sm:px-6 lg:px-8 2xl:px-12 py-3 sm:py-4">
          {editingPrompt ? (
            <div className="flex items-center gap-3">
              <button
                onClick={handleBackFromPromptSpace}
                className="flex items-center gap-1.5 text-surface-400 hover:text-white transition-colors px-2 py-1.5 rounded-lg hover:bg-surface-700/50"
              >
                <svg className="w-4 h-4" fill="none" stroke="currentColor" viewBox="0 0 24 24">
                  <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M10 19l-7-7m0 0l7-7m-7 7h18" />
                </svg>
                <span className="text-sm">Back</span>
              </button>
              <div className="h-5 w-px bg-surface-700" />
              <div className="w-10 h-10 rounded-xl bg-accent-500/20 flex items-center justify-center">
                <DocumentTextIcon className="w-5 h-5 text-accent-400" />
              </div>
              <div>
                <h2 className="text-lg sm:text-xl font-semibold text-white">{editingPrompt.sync_basename}</h2>
                <p className="text-xs sm:text-sm text-surface-400">
                  {editingPrompt.language ? `${editingPrompt.language} prompt` : 'Editing prompt'}
                </p>
              </div>
            </div>
          ) : (
            <>
          {view === 'devunits' && (
            <div className="flex flex-col sm:flex-row sm:items-center sm:justify-between gap-3">
              <div className="flex items-center gap-3">
                <div className="w-10 h-10 rounded-xl bg-[#FDCE49]/20 flex items-center justify-center">
                  <Squares2X2Icon className="w-5 h-5 text-[#FDCE49]" />
                </div>
                <div>
                  <h2 className="text-lg sm:text-xl font-semibold text-white">Dev Units</h2>
                  <p className="text-xs sm:text-sm text-surface-400">Manage your development modules and architecture</p>
                </div>
              </div>
              {/* Graph/List toggle */}
              <div className="flex bg-surface-800/60 p-1 rounded-lg border border-surface-700/50">
                <button
                  onClick={() => setDevUnitsSubView('graph')}
                  className={`px-3 sm:px-4 py-1.5 sm:py-2 rounded-md text-xs sm:text-sm font-medium transition-all duration-200 ${
                    devUnitsSubView === 'graph'
                      ? 'bg-[#DFA84A] text-surface-900 shadow-md'
                      : 'text-surface-300 hover:text-white hover:bg-surface-700/50'
                  }`}
                >
                  <Squares2X2Icon className="inline w-4 h-4 mr-1.5" />Graph View
                </button>
                <button
                  onClick={() => setDevUnitsSubView('list')}
                  className={`px-3 sm:px-4 py-1.5 sm:py-2 rounded-md text-xs sm:text-sm font-medium transition-all duration-200 ${
                    devUnitsSubView === 'list'
                      ? 'bg-[#DFA84A] text-surface-900 shadow-md'
                      : 'text-surface-300 hover:text-white hover:bg-surface-700/50'
                  }`}
                >
                  <DocumentTextIcon className="inline w-4 h-4 mr-1.5" />List View
                </button>
              </div>
            </div>
          )}
          {view === 'bug' && (
            <div className="flex items-center gap-3">
              <div className="w-10 h-10 rounded-xl bg-red-500/20 flex items-center justify-center">
                <BugAntIcon className="w-5 h-5 text-red-400" />
              </div>
              <div>
                <h2 className="text-lg sm:text-xl font-semibold text-white">Bug Investigation Agent</h2>
                <p className="text-xs sm:text-sm text-surface-400">Automatically investigate GitHub issues and generate failing test cases</p>
              </div>
            </div>
          )}
          {view === 'fix' && (
            <div className="flex items-center gap-3">
              <div className="w-10 h-10 rounded-xl bg-blue-500/20 flex items-center justify-center">
                <svg className="w-5 h-5 text-blue-400" fill="none" stroke="currentColor" viewBox="0 0 24 24">
                  <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M11 5H6a2 2 0 00-2 2v11a2 2 0 002 2h11a2 2 0 002-2v-5m-1.414-9.414a2 2 0 112.828 2.828L11.828 15H9v-2.828l8.586-8.586z" />
                </svg>
              </div>
              <div>
                <h2 className="text-lg sm:text-xl font-semibold text-white">PR Fix Agent</h2>
                <p className="text-xs sm:text-sm text-surface-400">Automatically fix code issues based on PR review comments</p>
              </div>
            </div>
          )}
          {view === 'change' && (
            <div className="flex items-center gap-3">
              <div className="w-10 h-10 rounded-xl bg-purple-500/20 flex items-center justify-center">
                <svg className="w-5 h-5 text-purple-400" fill="none" stroke="currentColor" viewBox="0 0 24 24">
                  <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M12 6V4m0 2a2 2 0 100 4m0-4a2 2 0 110 4m-6 8a2 2 0 100-4m0 4a2 2 0 110-4m0 4v2m0-6V4m6 6v10m6-2a2 2 0 100-4m0 4a2 2 0 110-4m0 4v2m0-6V4" />
                </svg>
              </div>
              <div>
                <h2 className="text-lg sm:text-xl font-semibold text-white">Change Request Agent</h2>
                <p className="text-xs sm:text-sm text-surface-400">Automatically implement feature requests and changes from GitHub issues</p>
              </div>
            </div>
          )}
          {view === 'settings' && (
            <div className="flex items-center gap-3">
              <div className="w-10 h-10 rounded-xl bg-surface-700/50 flex items-center justify-center">
                <Cog6ToothIcon className="w-5 h-5 text-surface-300" />
              </div>
              <div>
                <h2 className="text-lg sm:text-xl font-semibold text-white">Settings</h2>
                <p className="text-xs sm:text-sm text-surface-400">Configure project settings and preferences</p>
              </div>
            </div>
          )}
            </>
          )}
        </div>
      </div>

      {/* Main content - PromptSpace when editing, otherwise regular views */}
      {editingPrompt ? (
        <div className="flex-1 flex flex-col" style={{ height: 'calc(100vh - 8.5rem)' }}>
          <PromptSpace
            prompt={editingPrompt}
            onBack={handleBackFromPromptSpace}
            onRunCommand={handlePromptSpaceCommand}
            onAddToQueue={handlePromptSpaceAddToQueue}
            isExecuting={isExecuting}
            executionStatus={executionStatus}
            lastCommand={lastCommand}
            lastRunResult={lastRunResult}
            onCancelCommand={handleCancelCommand}
            embedded
          />
        </div>
      ) : (
      <main className="mx-auto px-4 sm:px-6 lg:px-8 2xl:px-12 py-4 sm:py-6 pb-16 sm:pb-20">
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

        {view === 'devunits' ? (
          <div className="animate-fade-in">

            {devUnitsSubView === 'graph' ? (
              <ArchitectureView
                serverConnected={serverConnected}
                isExecuting={isExecuting}
                onOpenPromptSpace={handleOpenPromptSpace}
                onBatchStart={handleBatchOperationStart}
                onBatchProgress={handleBatchOperationProgress}
                onBatchComplete={handleBatchOperationComplete}
                executionMode={executionMode}
                selectedRemoteSession={selectedRemoteSession}
                onRemoteJobSubmitted={(displayCommand, commandType, commandId, sessionId) => {
                  addSpawnedJob(displayCommand, commandType, commandId, { remote: true, sessionId });
                }}
                onAddToQueue={handleAddToQueue}
                onRunSync={(prompt, options) => handleRunCommand(CommandType.SYNC, prompt, options)}
                syncCompletedCounter={syncCompletedCounter}
              />
            ) : (
              <div>
                <PromptSelector
                  onEditPrompt={(prompt) => { setSelectedPrompt(prompt); handleOpenPromptSpace(prompt); }}
                  onCreatePrompt={handleOpenPromptSpace}
                  onRunSync={(prompt, options) => handleRunCommand(CommandType.SYNC, prompt, options)}
                  onAddToQueue={(prompt, options) => {
                    const rawOptions = options || {};
                    const displayCommand = buildDisplayCommand(CommandType.SYNC, prompt, rawOptions);
                    handleAddToQueue(CommandType.SYNC, prompt, rawOptions, displayCommand);
                  }}
                  selectedPrompt={selectedPrompt}
                />
              </div>
            )}
          </div>
        ) : view === 'settings' ? (
          <div className="animate-fade-in">
            <ProjectSettings />
          </div>
        ) : view === 'bug' ? (
          <div className="max-w-6xl mx-auto animate-fade-in">
            <div className="grid gap-4 md:grid-cols-2">
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
                  Agent Workflow (10 Steps)
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
                    { step: 9, name: 'E2E Test', desc: 'Run end-to-end tests to verify fix' },
                    { step: 10, name: 'Create PR', desc: 'Open a draft pull request' },
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
        ) : view === 'fix' ? (
          <div className="max-w-6xl mx-auto animate-fade-in">
            <div className="grid gap-4 md:grid-cols-2">
              {/* Left column: Input and action */}
              <div className="space-y-4">
                {/* Main input card */}
                <div className="glass rounded-2xl p-4 sm:p-6 border border-surface-700/50">
                  <label className="block text-sm font-medium text-surface-300 mb-2">
                    GitHub PR URL
                  </label>
                  <input
                    type="url"
                    value={fixPrUrl}
                    onChange={(e) => setFixPrUrl(e.target.value)}
                    placeholder="https://github.com/org/repo/pull/123"
                    className="w-full px-3 sm:px-4 py-2.5 sm:py-3 bg-surface-900/50 border border-surface-600 rounded-xl text-white placeholder-surface-500 focus:outline-none focus:border-accent-500 focus:ring-1 focus:ring-accent-500/50 transition-all text-sm sm:text-base"
                    disabled={isExecuting}
                  />

                  <button
                    onClick={handleRunFixCommand}
                    disabled={isExecuting || !serverConnected || !fixPrUrl.trim()}
                    className={`
                      mt-4 w-full px-4 py-2.5 sm:py-3 rounded-xl font-medium transition-all duration-200 flex items-center justify-center gap-2 text-sm sm:text-base
                      ${isExecuting || !serverConnected || !fixPrUrl.trim()
                        ? 'bg-surface-700 text-surface-500 cursor-not-allowed'
                        : 'bg-gradient-to-r from-blue-600 to-blue-500 hover:from-blue-500 hover:to-blue-400 text-white shadow-lg shadow-blue-500/25 hover:shadow-blue-500/40'}
                    `}
                  >
                    <svg className="w-4 h-4" fill="none" stroke="currentColor" viewBox="0 0 24 24">
                      <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M11 5H6a2 2 0 00-2 2v11a2 2 0 002 2h11a2 2 0 002-2v-5m-1.414-9.414a2 2 0 112.828 2.828L11.828 15H9v-2.828l8.586-8.586z" />
                    </svg>
                    <span>Start Fix</span>
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
                      <span><strong className="text-surface-300">PR has review comments</strong> - The agent analyzes review comments to understand what needs fixing</span>
                    </li>
                  </ul>
                </div>

                {/* After fix card */}
                <div className="glass rounded-2xl p-4 sm:p-5 border border-surface-700/50">
                  <h3 className="text-sm font-semibold text-white mb-3 flex items-center gap-2">
                    <svg className="w-4 h-4 text-green-400" fill="none" stroke="currentColor" viewBox="0 0 24 24">
                      <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M9 12l2 2 4-4m6 2a9 9 0 11-18 0 9 9 0 0118 0z" />
                    </svg>
                    After Fix
                  </h3>
                  <ul className="space-y-2 text-xs text-surface-400">
                    <li className="flex items-start gap-2">
                      <span className="text-green-400">1.</span>
                      <span><strong className="text-surface-300">Review the changes</strong> - The agent commits fixes addressing review comments</span>
                    </li>
                    <li className="flex items-start gap-2">
                      <span className="text-green-400">2.</span>
                      <span><strong className="text-surface-300">Run tests</strong> - Verify the fixes don't break existing functionality</span>
                    </li>
                    <li className="flex items-start gap-2">
                      <span className="text-green-400">3.</span>
                      <span><strong className="text-surface-300">Push changes</strong> - Push the fix commits to update the PR</span>
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
                  Agent Workflow
                </h3>
                <div className="space-y-1">
                  {[
                    { step: 1, name: 'Fetch PR Details', desc: 'Get PR information and review comments' },
                    { step: 2, name: 'Analyze Comments', desc: 'Understand what changes are requested' },
                    { step: 3, name: 'Locate Code', desc: 'Find the relevant code sections to fix' },
                    { step: 4, name: 'Plan Changes', desc: 'Design the fix approach' },
                    { step: 5, name: 'Apply Fixes', desc: 'Make the necessary code changes' },
                    { step: 6, name: 'Verify Changes', desc: 'Ensure fixes address the comments' },
                    { step: 7, name: 'Commit', desc: 'Create commits with fix descriptions' },
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
                    <strong className="text-surface-400">Note:</strong> The agent focuses on addressing review comments.
                    Progress is shown in the terminal.
                  </p>
                </div>
              </div>
            </div>
          </div>
        ) : view === 'change' ? (
          <div className="max-w-6xl mx-auto animate-fade-in">
            <div className="grid gap-4 md:grid-cols-2">
              {/* Left column: Input and action */}
              <div className="space-y-4">
                {/* Main input card */}
                <div className="glass rounded-2xl p-4 sm:p-6 border border-surface-700/50">
                  <label className="block text-sm font-medium text-surface-300 mb-2">
                    GitHub Issue URL
                  </label>
                  <input
                    type="url"
                    value={changeIssueUrl}
                    onChange={(e) => setChangeIssueUrl(e.target.value)}
                    placeholder="https://github.com/org/repo/issues/123"
                    className="w-full px-3 sm:px-4 py-2.5 sm:py-3 bg-surface-900/50 border border-surface-600 rounded-xl text-white placeholder-surface-500 focus:outline-none focus:border-accent-500 focus:ring-1 focus:ring-accent-500/50 transition-all text-sm sm:text-base"
                    disabled={isExecuting}
                  />

                  <button
                    onClick={handleRunChangeCommand}
                    disabled={isExecuting || !serverConnected || !changeIssueUrl.trim()}
                    className={`
                      mt-4 w-full px-4 py-2.5 sm:py-3 rounded-xl font-medium transition-all duration-200 flex items-center justify-center gap-2 text-sm sm:text-base
                      ${isExecuting || !serverConnected || !changeIssueUrl.trim()
                        ? 'bg-surface-700 text-surface-500 cursor-not-allowed'
                        : 'bg-gradient-to-r from-purple-600 to-purple-500 hover:from-purple-500 hover:to-purple-400 text-white shadow-lg shadow-purple-500/25 hover:shadow-purple-500/40'}
                    `}
                  >
                    <svg className="w-4 h-4" fill="none" stroke="currentColor" viewBox="0 0 24 24">
                      <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M12 6V4m0 2a2 2 0 100 4m0-4a2 2 0 110 4m-6 8a2 2 0 100-4m0 4a2 2 0 110-4m0 4v2m0-6V4m6 6v10m6-2a2 2 0 100-4m0 4a2 2 0 110-4m0 4v2m0-6V4" />
                    </svg>
                    <span>Start Implementation</span>
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
                      <span><strong className="text-surface-300">Clear requirements</strong> - The issue should describe the desired change clearly</span>
                    </li>
                  </ul>
                </div>

                {/* After change card */}
                <div className="glass rounded-2xl p-4 sm:p-5 border border-surface-700/50">
                  <h3 className="text-sm font-semibold text-white mb-3 flex items-center gap-2">
                    <svg className="w-4 h-4 text-green-400" fill="none" stroke="currentColor" viewBox="0 0 24 24">
                      <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M9 12l2 2 4-4m6 2a9 9 0 11-18 0 9 9 0 0118 0z" />
                    </svg>
                    After Implementation
                  </h3>
                  <ul className="space-y-2 text-xs text-surface-400">
                    <li className="flex items-start gap-2">
                      <span className="text-green-400">1.</span>
                      <span><strong className="text-surface-300">Review the draft PR</strong> - The agent creates a draft PR with the implementation</span>
                    </li>
                    <li className="flex items-start gap-2">
                      <span className="text-green-400">2.</span>
                      <span><strong className="text-surface-300">Test the changes</strong> - Verify the implementation works as expected</span>
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
                  Agent Workflow
                </h3>
                <div className="space-y-1">
                  {[
                    { step: 1, name: 'Fetch Issue', desc: 'Get issue details and requirements' },
                    { step: 2, name: 'Analyze Requirements', desc: 'Understand what needs to be implemented' },
                    { step: 3, name: 'Explore Codebase', desc: 'Find relevant code and patterns' },
                    { step: 4, name: 'Plan Implementation', desc: 'Design the approach and changes needed' },
                    { step: 5, name: 'Implement Changes', desc: 'Write the code for the feature' },
                    { step: 6, name: 'Add Tests', desc: 'Create tests for the new functionality' },
                    { step: 7, name: 'Verify', desc: 'Run tests and verify implementation' },
                    { step: 8, name: 'Create PR', desc: 'Open a draft pull request' },
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
                    <strong className="text-surface-400">Note:</strong> The agent analyzes the issue and implements the requested changes.
                    Progress is shown in the terminal.
                  </p>
                </div>
              </div>
            </div>
          </div>
        ) : null}
      </main>
      )}

      {/* Job Dashboard - shows active and completed jobs, only when Jobs button clicked */}
      <JobDashboard
        activeJobs={activeJobs}
        completedJobs={completedJobs}
        selectedJob={selectedJob}
        onSelectJob={setSelectedJobId}
        onCancelJob={cancelJob}
        onRemoveJob={removeJob}
        onClearCompleted={clearCompletedJobs}
        onMarkSpawnedDone={markSpawnedJobDone}
        onMarkJobStatus={markJobStatus}
        batchOperation={batchOperation}
        onCancelBatchOperation={handleCancelBatchOperation}
        isVisible={showJobsDashboard}
        onClose={() => setShowJobsDashboard(false)}
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
        <div className="mx-auto px-4 sm:px-6 lg:px-8 2xl:px-12 flex items-center justify-center gap-2 text-xs text-surface-500">
          <span className="w-4 h-4 rounded bg-surface-800/80 flex items-center justify-center p-0.5">
            <svg viewBox="0 0 1024 1024" className="w-full h-full" xmlns="http://www.w3.org/2000/svg">
              <g stroke="#00e3ff" strokeWidth="70" strokeLinecap="round" strokeLinejoin="round" fill="none">
                <path d="M 260 180 H 600 A 230 230 0 0 1 600 660 H 480 L 260 880 V 180 Z"/>
                <polyline points="505 340 585 420 505 500"/>
              </g>
            </svg>
          </span>
          <span className="hidden sm:inline">Prompt Driven</span>
          <span className="sm:hidden">PDD</span>
          <span className="text-surface-600">•</span>
          <span>{isAnyJobRunning ? 'Jobs running - click Jobs button above' : 'Commands tracked in dashboard'}</span>
        </div>
      </footer>

      {/* Re-authentication modal */}
      {showReauthModal && (
        <ReauthModal onClose={() => setShowReauthModal(false)} />
      )}

      {/* Device indicator for responsive testing (dev only) */}
      <DeviceIndicator />
    </div>
    </ErrorBoundary>
  );
};

export default App;
