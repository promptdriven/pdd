/**
 * TaskQueuePanel - Main container for the task queue.
 *
 * Layout:
 * - Collapsible panel showing queued tasks
 * - Execution mode toggle (Auto/Manual)
 * - Control buttons (Start, Pause, Clear, etc.)
 * - Draggable panel that can be repositioned
 */

import React, { useState, useCallback, useEffect, useRef } from 'react';
import { TaskQueueItem as TaskItem, ExecutionMode } from '../hooks/useTaskQueue';
import TaskQueueItemComponent from './TaskQueueItem';
import TaskQueueControls from './TaskQueueControls';

// Storage key for panel position
const PANEL_POSITION_KEY = 'pdd-task-queue-position';

interface PanelPosition {
  x: number;
  y: number;
}

const getDefaultPosition = (): PanelPosition => ({
  x: window.innerWidth - 380 - 16, // right-4 equivalent
  y: 64, // top-16 equivalent
});

const loadSavedPosition = (): PanelPosition | null => {
  try {
    const saved = localStorage.getItem(PANEL_POSITION_KEY);
    if (saved) {
      const pos = JSON.parse(saved);
      // Validate the position is within viewport bounds
      if (typeof pos.x === 'number' && typeof pos.y === 'number') {
        return {
          x: Math.max(0, Math.min(pos.x, window.innerWidth - 100)),
          y: Math.max(0, Math.min(pos.y, window.innerHeight - 100)),
        };
      }
    }
  } catch (e) {
    console.warn('Failed to load panel position:', e);
  }
  return null;
};

const savePosition = (pos: PanelPosition) => {
  try {
    localStorage.setItem(PANEL_POSITION_KEY, JSON.stringify(pos));
  } catch (e) {
    console.warn('Failed to save panel position:', e);
  }
};

interface TaskQueuePanelProps {
  tasks: TaskItem[];
  executionMode: ExecutionMode;
  isQueueRunning: boolean;
  isPaused: boolean;
  progress: {
    total: number;
    completed: number;
    pending: number;
    running: number;
  };
  onSetExecutionMode: (mode: ExecutionMode) => void;
  onStartQueue: () => void;
  onPauseQueue: () => void;
  onResumeQueue: () => void;
  onRunNextTask: () => void;
  onRemoveTask: (taskId: string) => void;
  onSkipTask: (taskId: string) => void;
  onRetryTask: (taskId: string) => void;
  onReorderTasks: (fromIndex: number, toIndex: number) => void;
  onClearCompleted: () => void;
  onClearAll: () => void;
}

const TaskQueuePanel: React.FC<TaskQueuePanelProps> = ({
  tasks,
  executionMode,
  isQueueRunning,
  isPaused,
  progress,
  onSetExecutionMode,
  onStartQueue,
  onPauseQueue,
  onResumeQueue,
  onRunNextTask,
  onRemoveTask,
  onSkipTask,
  onRetryTask,
  onReorderTasks,
  onClearCompleted,
  onClearAll,
}) => {
  const [isCollapsed, setIsCollapsed] = useState(false);
  const [draggedIndex, setDraggedIndex] = useState<number | null>(null);

  // Panel position state for drag-to-move functionality
  const [position, setPosition] = useState<PanelPosition>(() => loadSavedPosition() || getDefaultPosition());
  const [isDraggingPanel, setIsDraggingPanel] = useState(false);
  const dragStartRef = useRef<{ mouseX: number; mouseY: number; panelX: number; panelY: number } | null>(null);
  const panelRef = useRef<HTMLDivElement>(null);

  // Handle window resize to keep panel in bounds
  useEffect(() => {
    const handleResize = () => {
      setPosition(prev => ({
        x: Math.max(0, Math.min(prev.x, window.innerWidth - 100)),
        y: Math.max(0, Math.min(prev.y, window.innerHeight - 100)),
      }));
    };
    window.addEventListener('resize', handleResize);
    return () => window.removeEventListener('resize', handleResize);
  }, []);

  // Panel drag handlers
  const handlePanelDragStart = useCallback((e: React.MouseEvent) => {
    // Only start drag if clicking the drag handle area
    if ((e.target as HTMLElement).closest('[data-drag-handle]')) {
      e.preventDefault();
      setIsDraggingPanel(true);
      dragStartRef.current = {
        mouseX: e.clientX,
        mouseY: e.clientY,
        panelX: position.x,
        panelY: position.y,
      };
    }
  }, [position]);

  useEffect(() => {
    if (!isDraggingPanel) return;

    const handleMouseMove = (e: MouseEvent) => {
      if (!dragStartRef.current) return;

      const deltaX = e.clientX - dragStartRef.current.mouseX;
      const deltaY = e.clientY - dragStartRef.current.mouseY;

      const newX = Math.max(0, Math.min(dragStartRef.current.panelX + deltaX, window.innerWidth - 100));
      const newY = Math.max(0, Math.min(dragStartRef.current.panelY + deltaY, window.innerHeight - 100));

      setPosition({ x: newX, y: newY });
    };

    const handleMouseUp = () => {
      setIsDraggingPanel(false);
      dragStartRef.current = null;
      // Save position when drag ends
      setPosition(pos => {
        savePosition(pos);
        return pos;
      });
    };

    document.addEventListener('mousemove', handleMouseMove);
    document.addEventListener('mouseup', handleMouseUp);

    return () => {
      document.removeEventListener('mousemove', handleMouseMove);
      document.removeEventListener('mouseup', handleMouseUp);
    };
  }, [isDraggingPanel]);

  // Reset position to default (top-right corner)
  const resetPosition = useCallback(() => {
    const defaultPos = getDefaultPosition();
    setPosition(defaultPos);
    savePosition(defaultPos);
  }, []);

  // All hooks must be called before any early returns!
  // Drag handlers - defined unconditionally
  const handleDragStart = useCallback((index: number) => (e: React.DragEvent) => {
    // Only allow dragging pending tasks
    if (!tasks || !tasks[index] || tasks[index].status !== 'pending') {
      e.preventDefault();
      return;
    }
    setDraggedIndex(index);
    e.dataTransfer.effectAllowed = 'move';
  }, [tasks]);

  const handleDragOver = useCallback((index: number) => (e: React.DragEvent) => {
    e.preventDefault();
    if (draggedIndex === null || draggedIndex === index) return;
    // Only allow dropping on pending tasks
    if (!tasks || !tasks[index] || tasks[index].status !== 'pending') return;
    e.dataTransfer.dropEffect = 'move';
  }, [draggedIndex, tasks]);

  const handleDrop = useCallback((index: number) => (e: React.DragEvent) => {
    e.preventDefault();
    if (draggedIndex === null || draggedIndex === index) return;
    // Only allow dropping on pending tasks
    if (!tasks || !tasks[index] || tasks[index].status !== 'pending') return;
    onReorderTasks(draggedIndex, index);
    setDraggedIndex(null);
  }, [draggedIndex, onReorderTasks, tasks]);

  const handleDragEnd = useCallback(() => {
    setDraggedIndex(null);
  }, []);

  // Safety check - ensure tasks is an array (after all hooks)
  if (!Array.isArray(tasks)) {
    console.error('TaskQueuePanel: tasks is not an array', tasks);
    return null;
  }

  // Derived state
  const hasPendingTasks = tasks.some(t => t?.status === 'pending');
  const hasCompletedTasks = tasks.some(t => t?.status === 'completed' || t?.status === 'failed' || t?.status === 'skipped');
  const hasAnyTasks = tasks.length > 0;

  // Don't render if no tasks
  if (!hasAnyTasks) {
    return null;
  }

  return (
    <div
      ref={panelRef}
      className={`fixed z-40 pointer-events-none ${isDraggingPanel ? 'select-none' : ''}`}
      style={{
        width: '380px',
        left: `${position.x}px`,
        top: `${position.y}px`,
      }}
    >
      <div
        className={`
          pointer-events-auto bg-surface-900/95 backdrop-blur-lg rounded-2xl border border-surface-700/50 shadow-2xl
          transition-[max-height] duration-300 ease-in-out
          ${isCollapsed ? 'max-h-14' : 'max-h-[70vh]'}
          ${isDraggingPanel ? 'cursor-grabbing' : ''}
        `}
      >
        {/* Header bar */}
        <div
          className="flex items-center justify-between px-4 py-3 border-b border-surface-700/50"
          onMouseDown={handlePanelDragStart}
        >
          <div className="flex items-center gap-2">
            {/* Drag handle */}
            <div
              data-drag-handle
              className="text-surface-500 hover:text-surface-300 cursor-grab active:cursor-grabbing p-1 -ml-1"
              title="Drag to move panel"
            >
              <svg className="w-4 h-4" fill="none" stroke="currentColor" viewBox="0 0 24 24">
                <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M4 8h16M4 16h16" />
              </svg>
            </div>

            {/* Toggle icon */}
            <button
              onClick={() => setIsCollapsed(!isCollapsed)}
              className="text-surface-400 hover:text-surface-300 transition-colors"
              title={isCollapsed ? 'Expand' : 'Collapse'}
            >
              <svg
                className={`w-4 h-4 transition-transform ${isCollapsed ? '' : 'rotate-180'}`}
                fill="none"
                stroke="currentColor"
                viewBox="0 0 24 24"
              >
                <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M5 15l7-7 7 7" />
              </svg>
            </button>

            <h2 className="text-sm font-medium text-white flex items-center gap-2">
              <svg className="w-4 h-4" fill="none" stroke="currentColor" viewBox="0 0 24 24">
                <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M9 5H7a2 2 0 00-2 2v12a2 2 0 002 2h10a2 2 0 002-2V7a2 2 0 00-2-2h-2M9 5a2 2 0 002 2h2a2 2 0 002-2M9 5a2 2 0 012-2h2a2 2 0 012 2m-6 9l2 2 4-4" />
              </svg>
              Task Queue
            </h2>

            {/* Running indicator */}
            {isQueueRunning && !isPaused && (
              <span className="px-2 py-0.5 text-xs font-medium bg-accent-500/20 text-accent-400 rounded-full flex items-center gap-1">
                <svg className="animate-spin h-3 w-3" viewBox="0 0 24 24">
                  <circle className="opacity-25" cx="12" cy="12" r="10" stroke="currentColor" strokeWidth="4" fill="none" />
                  <path className="opacity-75" fill="currentColor" d="M4 12a8 8 0 018-8V0C5.373 0 0 5.373 0 12h4z" />
                </svg>
                Running
              </span>
            )}

            {/* Paused indicator */}
            {isQueueRunning && isPaused && (
              <span className="px-2 py-0.5 text-xs font-medium bg-yellow-500/20 text-yellow-400 rounded-full">
                Paused
              </span>
            )}

            {/* Task count badge */}
            <span className="px-2 py-0.5 text-xs font-medium bg-surface-700 text-surface-400 rounded-full">
              {progress.pending} pending
            </span>
          </div>

          {/* Mode indicator and reset button */}
          <div className="flex items-center gap-2">
            <span className={`px-2 py-0.5 text-xs font-medium rounded-full ${
              executionMode === 'auto'
                ? 'bg-green-500/20 text-green-400'
                : 'bg-surface-700 text-surface-400'
            }`}>
              {executionMode === 'auto' ? 'Auto' : 'Manual'}
            </span>

            {/* Reset position button */}
            <button
              onClick={(e) => {
                e.stopPropagation();
                resetPosition();
              }}
              className="text-surface-500 hover:text-surface-300 p-1 rounded transition-colors"
              title="Reset panel position"
            >
              <svg className="w-3.5 h-3.5" fill="none" stroke="currentColor" viewBox="0 0 24 24">
                <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M4 4v5h.582m15.356 2A8.001 8.001 0 004.582 9m0 0H9m11 11v-5h-.581m0 0a8.003 8.003 0 01-15.357-2m15.357 2H15" />
              </svg>
            </button>
          </div>
        </div>

        {/* Content (hidden when collapsed) */}
        {!isCollapsed && (
          <div className="max-h-[calc(70vh-3.5rem)] overflow-hidden flex flex-col">
            {/* Controls */}
            <div className="px-4 py-3 border-b border-surface-700/30">
              <TaskQueueControls
                executionMode={executionMode}
                isQueueRunning={isQueueRunning}
                isPaused={isPaused}
                hasPendingTasks={hasPendingTasks}
                hasCompletedTasks={hasCompletedTasks}
                hasAnyTasks={hasAnyTasks}
                progress={progress}
                onSetExecutionMode={onSetExecutionMode}
                onStartQueue={onStartQueue}
                onPauseQueue={onPauseQueue}
                onResumeQueue={onResumeQueue}
                onRunNextTask={onRunNextTask}
                onClearCompleted={onClearCompleted}
                onClearAll={onClearAll}
              />
            </div>

            {/* Task list */}
            <div className="flex-1 overflow-y-auto p-4">
              <div className="space-y-2">
                {tasks.map((task, index) => {
                  if (!task || !task.id) return null;
                  return (
                    <TaskQueueItemComponent
                      key={task.id}
                      task={task}
                      index={index}
                      isDraggable={task.status === 'pending'}
                      onRemove={() => onRemoveTask(task.id)}
                      onSkip={() => onSkipTask(task.id)}
                      onRetry={() => onRetryTask(task.id)}
                      onRunNow={onRunNextTask}
                      onDragStart={handleDragStart(index)}
                      onDragOver={handleDragOver(index)}
                      onDrop={handleDrop(index)}
                      onDragEnd={handleDragEnd}
                    />
                  );
                })}
              </div>

              {/* Empty state */}
              {tasks.length === 0 && (
                <div className="text-center py-8">
                  <svg
                    className="w-12 h-12 text-surface-600 mx-auto mb-3"
                    fill="none"
                    stroke="currentColor"
                    viewBox="0 0 24 24"
                  >
                    <path
                      strokeLinecap="round"
                      strokeLinejoin="round"
                      strokeWidth={1.5}
                      d="M9 5H7a2 2 0 00-2 2v12a2 2 0 002 2h10a2 2 0 002-2V7a2 2 0 00-2-2h-2M9 5a2 2 0 002 2h2a2 2 0 002-2M9 5a2 2 0 012-2h2a2 2 0 012 2"
                    />
                  </svg>
                  <p className="text-surface-500 text-sm">Queue is empty</p>
                  <p className="text-surface-600 text-xs mt-1">
                    Add tasks to run them in sequence
                  </p>
                </div>
              )}
            </div>
          </div>
        )}
      </div>
    </div>
  );
};

export default TaskQueuePanel;
