import React, { memo } from 'react';
import { Handle, Position, NodeProps } from 'reactflow';
import { ArchitectureModule, PromptInfo } from '../api';
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
  // Edit mode props
  editMode?: boolean;
  onEdit?: (module: ArchitectureModule) => void;
  onDelete?: (filename: string) => void;
  isHighlighted?: boolean;  // For error highlighting (e.g., circular dependencies)
}

const ModuleNode: React.FC<NodeProps<ModuleNodeData>> = ({ data, selected }) => {
  const { label, module, promptInfo, hasPrompt, colors, onClick, editMode, onEdit, isHighlighted } = data;
  const hasCode = !!promptInfo?.code;
  const hasTest = !!promptInfo?.test;
  const hasExample = !!promptInfo?.example;

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
          `}
          style={{ width: 200, minHeight: 70 }}
        >
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

          {/* Prompt status indicator */}
          {hasPrompt && (
            <div className="absolute -top-1.5 -right-1.5 w-5 h-5 bg-emerald-500 rounded-full flex items-center justify-center shadow-lg z-10">
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
