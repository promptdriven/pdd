import React, { memo } from 'react';
import { Handle, Position, NodeProps, useViewport } from 'reactflow';
import { ArchitectureModule, PromptInfo } from '../api';
import { getCompactFontPx } from './DependencyViewer';
import Tooltip from './Tooltip';

export interface ModuleNodeData {
  label: string;
  module: ArchitectureModule;
  promptInfo?: PromptInfo;
  hasPrompt: boolean;
  colors: {
    bg: string;
    border: string;
    hover: string;
    text: string;
  };
  onClick?: (module: ArchitectureModule) => void;
  onRunSync?: (module: ArchitectureModule) => void;  // Run pdd sync command
  // Edit mode props
  editMode?: boolean;
  onEdit?: (module: ArchitectureModule) => void;
  onDelete?: (filename: string) => void;
  isHighlighted?: boolean;  // For error highlighting (e.g., circular dependencies)
  isDimmed?: boolean;       // For focus mode (dims non-neighborhood nodes)
  // Batch (connected component) info
  batchId?: number;
  batchColor?: string;
  batchName?: string;
}


const ModuleNode: React.FC<NodeProps<ModuleNodeData>> = ({ data, selected, xPos, yPos }) => {
  const { label, module, promptInfo, hasPrompt, colors, onClick, onRunSync, editMode, onEdit, isHighlighted, isDimmed } = data;
  const hasCode = !!promptInfo?.code;
  const hasTest = !!promptInfo?.test;
  const hasExample = !!promptInfo?.example;
  const { zoom } = useViewport();
  const isCompact = zoom < 0.5;

  const handleClick = () => {
    if (onClick) {
      onClick(module);
    }
  };

  const handleEditClick = (e: React.MouseEvent) => {
    e.stopPropagation();
    if (onEdit) {
      onEdit(module);
    }
  };

  const handleSyncClick = (e: React.MouseEvent) => {
    e.stopPropagation();
    if (onRunSync) {
      onRunSync(module);
    }
  };

  if (isCompact) {
    return (
      <>
        <Handle type="target" position={Position.Top} className="!bg-blue-400 !w-1.5 !h-1.5" />
        <div
          onClick={handleClick}
          className={`
            px-2 py-1 rounded-lg border cursor-pointer transition-all duration-200
            ${colors.bg} ${colors.border}
            ${isDimmed ? 'opacity-20' : 'opacity-90'}
          `}
          style={{ width: 200, minHeight: 28 }}
        >
          <p
            className="font-medium text-white truncate"
            style={{ fontSize: `${getCompactFontPx(zoom)}px` }}
          >
            {label}
          </p>
        </div>
        <Handle type="source" position={Position.Bottom} className="!bg-blue-400 !w-1.5 !h-1.5" />
      </>
    );
  }

  return (
    <>
      <Handle type="target" position={Position.Top} className="!bg-blue-400 !w-2 !h-2" />

      <Tooltip
        content={
          <div className="max-w-xs">
            <div className="font-medium">{module.filename}</div>
            <div className="text-xs text-surface-400 mt-1">{module.filepath}</div>
            <div className="text-xs mt-2">{module.description?.substring(0, 100)}...</div>
            {hasPrompt && (
              <div className="mt-2 pt-2 border-t border-surface-700/50">
                <div className="text-xs text-emerald-400 flex items-center gap-1 mb-1">
                  <svg className="w-3 h-3" fill="none" stroke="currentColor" viewBox="0 0 24 24">
                    <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M5 13l4 4L19 7" />
                  </svg>
                  Prompt exists
                </div>
                <div className="flex items-center gap-2 text-xs mt-1">
                  <span className={hasCode ? 'text-green-400' : 'text-surface-500'}>{hasCode ? '✓' : '✗'} Code</span>
                  <span className={hasTest ? 'text-yellow-400' : 'text-surface-500'}>{hasTest ? '✓' : '✗'} Test</span>
                  <span className={hasExample ? 'text-blue-400' : 'text-surface-500'}>{hasExample ? '✓' : '✗'} Example</span>
                </div>
              </div>
            )}
          </div>
        }
      >
        <div
          onClick={handleClick}
          className={`
            relative px-4 py-3 rounded-xl border cursor-pointer
            transition-all duration-200 hover:scale-105 group
            ${colors.bg} ${colors.border} ${colors.hover}
            ${hasPrompt ? 'ring-2 ring-emerald-500/50' : ''}
            ${selected ? 'ring-2 ring-accent-500' : ''}
            ${isHighlighted ? 'ring-2 ring-red-500 animate-pulse' : ''}
            backdrop-blur-sm
          `}
          style={{ width: 200, minHeight: 85, opacity: isDimmed ? 0.25 : 0.95, transition: 'opacity 0.2s' }}
        >
          {/* Batch color stripe indicator */}
          {data.batchColor && (
            <div
              className="absolute -left-1.5 top-1/2 -translate-y-1/2 w-1.5 h-10 rounded-full"
              style={{ backgroundColor: data.batchColor }}
              title={data.batchName || `Batch ${data.batchId}`}
            />
          )}

          {/* Edit button overlay - only visible in edit mode on hover */}
          {editMode && (
            <button
              onClick={handleEditClick}
              className="absolute -top-2 -left-2 w-6 h-6 bg-accent-600 hover:bg-accent-500 rounded-full flex items-center justify-center shadow-lg z-20 opacity-0 group-hover:opacity-100 transition-opacity"
              title="Edit module"
            >
              <svg className="w-3 h-3 text-white" fill="none" stroke="currentColor" viewBox="0 0 24 24">
                <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M15.232 5.232l3.536 3.536m-2.036-5.036a2.5 2.5 0 113.536 3.536L6.5 21.036H3v-3.572L16.732 3.732z" />
              </svg>
            </button>
          )}

          {/* Sync button - run pdd sync command (only when prompt exists and not in edit mode) */}
          {hasPrompt && onRunSync && !editMode && (
            <button
              onClick={handleSyncClick}
              className="absolute -top-2 -right-2 w-6 h-6 bg-gradient-to-br from-[#FDCE49] to-[#DFA84A] hover:from-[#FFD966] hover:to-[#FDCE49] rounded-full flex items-center justify-center shadow-lg z-20 transition-all hover:scale-110"
              title="Run pdd sync (prompt → code)"
            >
              <svg className="w-3 h-3 text-surface-900" fill="none" stroke="currentColor" viewBox="0 0 24 24">
                <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2.5} d="M4 4v5h.582m15.356 2A8.001 8.001 0 004.582 9m0 0H9m11 11v-5h-.581m0 0a8.003 8.003 0 01-15.357-2m15.357 2H15" />
              </svg>
            </button>
          )}

          {/* Prompt status indicator - repositioned when sync button exists */}
          {hasPrompt && (
            <div className={`absolute ${onRunSync && !editMode ? '-top-1.5 right-5' : '-top-1.5 -right-1.5'} w-5 h-5 bg-emerald-500 rounded-full flex items-center justify-center shadow-lg z-10`}>
              <svg className="w-3 h-3 text-white" fill="none" stroke="currentColor" viewBox="0 0 24 24">
                <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={3} d="M5 13l4 4L19 7" />
              </svg>
            </div>
          )}

          {/* File status indicators */}
          {hasPrompt && (
            <div className="absolute -bottom-1.5 right-1 flex gap-0.5 z-10">
              <div
                className={`w-3.5 h-3.5 rounded-full flex items-center justify-center text-[8px] font-bold ${hasCode ? 'bg-green-500 text-white' : 'bg-surface-700 text-surface-500'}`}
                title={hasCode ? 'Code exists' : 'No code file'}
              >
                C
              </div>
              <div
                className={`w-3.5 h-3.5 rounded-full flex items-center justify-center text-[8px] font-bold ${hasTest ? 'bg-yellow-500 text-white' : 'bg-surface-700 text-surface-500'}`}
                title={hasTest ? 'Test exists' : 'No test file'}
              >
                T
              </div>
              <div
                className={`w-3.5 h-3.5 rounded-full flex items-center justify-center text-[8px] font-bold ${hasExample ? 'bg-blue-500 text-white' : 'bg-surface-700 text-surface-500'}`}
                title={hasExample ? 'Example exists' : 'No example file'}
              >
                E
              </div>
            </div>
          )}

          <p className="font-medium text-sm text-white truncate w-full">{label}</p>
          {process.env.NODE_ENV === 'development' && (
            <p
              className="text-[10px] text-surface-400 truncate w-full font-mono"
              title={`Position: (${Math.round(xPos)}, ${Math.round(yPos)})`}
            >
              x: {Math.round(xPos)}, y: {Math.round(yPos)}
            </p>
          )}
          <p className={`text-xs ${colors.text} truncate w-full`}>
            {module.interface?.type || 'module'}
          </p>
          <p className="text-xs text-surface-500 truncate w-full">
            Priority: {module.priority}
          </p>
        </div>
      </Tooltip>

      <Handle type="source" position={Position.Bottom} className="!bg-blue-400 !w-2 !h-2" />
    </>
  );
};

export default memo(ModuleNode);
