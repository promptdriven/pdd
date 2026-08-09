import React from 'react';
import Tooltip from './Tooltip';

interface GraphToolbarProps {
  editMode: boolean;
  hasUnsavedChanges: boolean;
  onToggleEditMode: () => void;
  onAddModule: () => void;
  onSave: () => void;
  onDiscard: () => void;
  onUndo: () => void;
  onRedo: () => void;
  canUndo: boolean;
  canRedo: boolean;
  isSaving?: boolean;
  onSyncFromPrompts?: () => void;  // New prop for sync button
  onRearrange?: () => void;
  isRearranging?: boolean;
  onManageGroups?: () => void;
}

const GraphToolbar: React.FC<GraphToolbarProps> = ({
  editMode,
  hasUnsavedChanges,
  onToggleEditMode,
  onAddModule,
  onSave,
  onDiscard,
  onUndo,
  onRedo,
  canUndo,
  canRedo,
  isSaving = false,
  onSyncFromPrompts,
  onRearrange,
  isRearranging = false,
  onManageGroups,
}) => {
  return (
    <div className="flex items-center gap-2 px-3 py-2 bg-surface-800/80 border-b border-surface-700/50">
      {/* Edit Mode Toggle — always first so it never shifts position */}
      <Tooltip content={editMode ? 'Exit edit mode' : 'Enter edit mode'}>
        <button
          onClick={onToggleEditMode}
          className={`
            flex items-center gap-1.5 px-3 py-1.5 rounded-lg text-xs font-medium transition-colors
            ${editMode
              ? 'bg-accent-600 text-white hover:bg-accent-500'
              : 'bg-surface-700 text-surface-300 hover:bg-surface-600'
            }
          `}
        >
          <svg className="w-3.5 h-3.5" fill="none" stroke="currentColor" viewBox="0 0 24 24">
            <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M15.232 5.232l3.536 3.536m-2.036-5.036a2.5 2.5 0 113.536 3.536L6.5 21.036H3v-3.572L16.732 3.732z" />
          </svg>
          <span>{editMode ? 'Editing' : 'Edit'}</span>
        </button>
      </Tooltip>

      {/* Sync from Prompts Button (only in view mode) */}
      {!editMode && onSyncFromPrompts && (
        <>
          <div className="w-px h-6 bg-surface-700" />
          <Tooltip content="Sync architecture.json from prompt metadata tags">
            <button
              onClick={onSyncFromPrompts}
              className="flex items-center gap-1.5 px-3 py-1.5 rounded-lg text-xs font-medium bg-purple-600 text-white hover:bg-purple-500 transition-colors"
            >
              <svg className="w-3.5 h-3.5" fill="none" stroke="currentColor" viewBox="0 0 24 24">
                <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M4 4v5h.582m15.356 2A8.001 8.001 0 004.582 9m0 0H9m11 11v-5h-.581m0 0a8.003 8.003 0 01-15.357-2m15.357 2H15" />
              </svg>
              <span>Sync from Prompts</span>
            </button>
          </Tooltip>
        </>
      )}

      {/* Edit mode actions */}
      {editMode && (
        <>
          <div className="w-px h-6 bg-surface-700" />

          {/* Add Module */}
          <Tooltip content="Add new module (N)">
            <button
              onClick={onAddModule}
              className="flex items-center gap-1.5 px-3 py-1.5 rounded-lg text-xs font-medium bg-emerald-600 text-white hover:bg-emerald-500 transition-colors"
            >
              <svg className="w-3.5 h-3.5" fill="none" stroke="currentColor" viewBox="0 0 24 24">
                <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M12 4v16m8-8H4" />
              </svg>
              <span>Add Module</span>
            </button>
          </Tooltip>

          {/* Manage Groups */}
          {onManageGroups && (
            <Tooltip content="Create or edit module groups for graph layout">
              <button
                onClick={onManageGroups}
                className="flex items-center gap-1.5 px-3 py-1.5 rounded-lg text-xs font-medium bg-violet-600 text-white hover:bg-violet-500 transition-colors"
              >
                <svg className="w-3.5 h-3.5" fill="none" stroke="currentColor" viewBox="0 0 24 24">
                  <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M19 11H5m14 0a2 2 0 012 2v6a2 2 0 01-2 2H5a2 2 0 01-2-2v-6a2 2 0 012-2m14 0V9a2 2 0 00-2-2M5 11V9a2 2 0 012-2m0 0V5a2 2 0 012-2h6a2 2 0 012 2v2M7 7h10" />
                </svg>
                <span>Groups</span>
              </button>
            </Tooltip>
          )}

          {/* Re-arrange Layout */}
          {onRearrange && (
            <>
              <div className="w-px h-6 bg-surface-700" />
              <Tooltip content="Re-arrange graph layout using AI (reads PRD + architecture file)">
                <button
                  onClick={onRearrange}
                  disabled={isRearranging}
                  className="flex items-center gap-1.5 px-3 py-1.5 rounded-lg text-xs font-medium bg-purple-600 text-white hover:bg-purple-500 disabled:opacity-50 disabled:cursor-not-allowed transition-colors"
                >
                  {isRearranging ? (
                    <svg className="w-3.5 h-3.5 animate-spin" fill="none" viewBox="0 0 24 24">
                      <circle className="opacity-25" cx="12" cy="12" r="10" stroke="currentColor" strokeWidth="4" />
                      <path className="opacity-75" fill="currentColor" d="M4 12a8 8 0 018-8V0C5.373 0 0 5.373 0 12h4zm2 5.291A7.962 7.962 0 014 12H0c0 3.042 1.135 5.824 3 7.938l3-2.647z" />
                    </svg>
                  ) : (
                    <svg className="w-3.5 h-3.5" fill="none" stroke="currentColor" viewBox="0 0 24 24">
                      <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M4 8V4m0 0h4M4 4l5 5m11-5h-4m4 0v4m0-4l-5 5M4 16v4m0 0h4m-4 0l5-5m11 5l-5-5m5 5v-4m0 4h-4" />
                    </svg>
                  )}
                  <span>{isRearranging ? 'Arranging…' : 'Re-arrange'}</span>
                </button>
              </Tooltip>
            </>
          )}

          <div className="w-px h-6 bg-surface-700" />

          {/* Undo */}
          <Tooltip content="Undo (Ctrl+Z)">
            <button
              onClick={onUndo}
              disabled={!canUndo}
              className="p-1.5 rounded-lg text-surface-300 hover:bg-surface-700 disabled:opacity-50 disabled:cursor-not-allowed transition-colors"
            >
              <svg className="w-4 h-4" fill="none" stroke="currentColor" viewBox="0 0 24 24">
                <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M3 10h10a8 8 0 018 8v2M3 10l6 6m-6-6l6-6" />
              </svg>
            </button>
          </Tooltip>

          {/* Redo */}
          <Tooltip content="Redo (Ctrl+Shift+Z)">
            <button
              onClick={onRedo}
              disabled={!canRedo}
              className="p-1.5 rounded-lg text-surface-300 hover:bg-surface-700 disabled:opacity-50 disabled:cursor-not-allowed transition-colors"
            >
              <svg className="w-4 h-4" fill="none" stroke="currentColor" viewBox="0 0 24 24">
                <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M21 10H11a8 8 0 00-8 8v2m18-10l-6 6m6-6l-6-6" />
              </svg>
            </button>
          </Tooltip>

          {/* Unsaved changes indicator and actions */}
          {hasUnsavedChanges && (
            <>
              <div className="w-px h-6 bg-surface-700" />
              <span className="text-xs text-yellow-400 flex items-center gap-1">
                <svg className="w-3 h-3" fill="currentColor" viewBox="0 0 20 20">
                  <path fillRule="evenodd" d="M8.257 3.099c.765-1.36 2.722-1.36 3.486 0l5.58 9.92c.75 1.334-.213 2.98-1.742 2.98H4.42c-1.53 0-2.493-1.646-1.743-2.98l5.58-9.92zM11 13a1 1 0 11-2 0 1 1 0 012 0zm-1-8a1 1 0 00-1 1v3a1 1 0 002 0V6a1 1 0 00-1-1z" clipRule="evenodd" />
                </svg>
                Unsaved changes
              </span>

              {/* Save */}
              <Tooltip content="Save changes (Ctrl+S)">
                <button
                  onClick={onSave}
                  disabled={isSaving}
                  className="flex items-center gap-1.5 px-3 py-1.5 rounded-lg text-xs font-medium bg-blue-600 text-white hover:bg-blue-500 disabled:opacity-50 disabled:cursor-not-allowed transition-colors"
                >
                  {isSaving ? (
                    <svg className="w-3.5 h-3.5 animate-spin" fill="none" viewBox="0 0 24 24">
                      <circle className="opacity-25" cx="12" cy="12" r="10" stroke="currentColor" strokeWidth="4" />
                      <path className="opacity-75" fill="currentColor" d="M4 12a8 8 0 018-8V0C5.373 0 0 5.373 0 12h4zm2 5.291A7.962 7.962 0 014 12H0c0 3.042 1.135 5.824 3 7.938l3-2.647z" />
                    </svg>
                  ) : (
                    <svg className="w-3.5 h-3.5" fill="none" stroke="currentColor" viewBox="0 0 24 24">
                      <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M8 7H5a2 2 0 00-2 2v9a2 2 0 002 2h14a2 2 0 002-2V9a2 2 0 00-2-2h-3m-1 4l-3 3m0 0l-3-3m3 3V4" />
                    </svg>
                  )}
                  <span>{isSaving ? 'Saving...' : 'Save'}</span>
                </button>
              </Tooltip>

              {/* Discard */}
              <Tooltip content="Discard changes (Escape)">
                <button
                  onClick={onDiscard}
                  className="flex items-center gap-1.5 px-3 py-1.5 rounded-lg text-xs font-medium bg-surface-700 text-surface-300 hover:bg-surface-600 transition-colors"
                >
                  <svg className="w-3.5 h-3.5" fill="none" stroke="currentColor" viewBox="0 0 24 24">
                    <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M6 18L18 6M6 6l12 12" />
                  </svg>
                  <span>Discard</span>
                </button>
              </Tooltip>
            </>
          )}
        </>
      )}
    </div>
  );
};

export default GraphToolbar;
