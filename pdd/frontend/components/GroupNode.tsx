import React, { memo } from 'react';
import { Handle, Position, NodeProps } from 'reactflow';
import { ArchitectureModule } from '../api';

export const GROUP_NODE_WIDTH = 220;
export const GROUP_NODE_HEIGHT = 40;

export interface GroupNodeData {
  groupName: string;
  modules: ArchitectureModule[];
  isExpanded: boolean;
  onToggle: (groupName: string) => void;
  existingPrompts?: Set<string>;
  editMode?: boolean;
  onEditGroup?: (groupName: string) => void;
}

const GroupNode: React.FC<NodeProps<GroupNodeData>> = ({ data }) => {
  const { groupName, modules, isExpanded, onToggle, existingPrompts = new Set(), editMode, onEditGroup } = data;
  const promptCount = modules.filter(m => existingPrompts.has(m.filename)).length;

  const handleToggle = (e: React.MouseEvent) => {
    e.stopPropagation();
    onToggle(groupName);
  };

  const handleEdit = (e: React.MouseEvent) => {
    e.stopPropagation();
    onEditGroup?.(groupName);
  };

  if (isExpanded) {
    return (
      <>
        <Handle type="target" position={Position.Top} className="!bg-violet-400 !w-2 !h-2" />
        <div
          className="flex items-center gap-2 px-3 rounded-lg border border-violet-500/60 bg-violet-900/40 backdrop-blur-sm group"
          style={{ width: GROUP_NODE_WIDTH, height: GROUP_NODE_HEIGHT }}
        >
          <button
            onClick={handleToggle}
            className="p-0.5 hover:bg-violet-700/50 rounded text-violet-400 hover:text-violet-200 transition-colors flex-shrink-0"
            title="Collapse group"
          >
            <svg className="w-3 h-3" fill="none" stroke="currentColor" viewBox="0 0 24 24">
              <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M5 15l7-7 7 7" />
            </svg>
          </button>
          <span className="text-xs font-semibold text-violet-300 uppercase tracking-wider truncate flex-1">
            {groupName}
          </span>
          <span className="text-[10px] text-violet-500 flex-shrink-0">{modules.length}m</span>
          {editMode && onEditGroup && (
            <button
              onClick={handleEdit}
              className="p-0.5 hover:bg-violet-700/50 rounded text-violet-500 hover:text-violet-300 transition-colors flex-shrink-0 opacity-0 group-hover:opacity-100"
              title="Edit group"
            >
              <svg className="w-3 h-3" fill="none" stroke="currentColor" viewBox="0 0 24 24">
                <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M15.232 5.232l3.536 3.536m-2.036-5.036a2.5 2.5 0 113.536 3.536L6.5 21.036H3v-3.572L16.732 3.732z" />
              </svg>
            </button>
          )}
        </div>
        <Handle type="source" position={Position.Bottom} className="!bg-violet-400 !w-2 !h-2" />
      </>
    );
  }

  // Collapsed: compact summary node
  return (
    <>
      <Handle type="target" position={Position.Top} className="!bg-violet-400 !w-2 !h-2" />
      <div
        onClick={handleToggle}
        className="relative px-4 py-3 rounded-xl border cursor-pointer transition-all duration-200 hover:scale-105 bg-violet-500/20 border-violet-500/50 hover:border-violet-400 backdrop-blur-sm group"
        style={{ width: 200, minHeight: 85 }}
      >
        {editMode && onEditGroup && (
          <button
            onClick={handleEdit}
            className="absolute -top-2 -left-2 w-6 h-6 bg-accent-600 hover:bg-accent-500 rounded-full flex items-center justify-center shadow-lg z-20 opacity-0 group-hover:opacity-100 transition-opacity"
            title="Edit group"
          >
            <svg className="w-3 h-3 text-white" fill="none" stroke="currentColor" viewBox="0 0 24 24">
              <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M15.232 5.232l3.536 3.536m-2.036-5.036a2.5 2.5 0 113.536 3.536L6.5 21.036H3v-3.572L16.732 3.732z" />
            </svg>
          </button>
        )}
        <div className="flex items-center justify-between mb-1">
          <span className="text-xs font-semibold text-violet-300 uppercase tracking-wider truncate flex-1">
            {groupName}
          </span>
          <svg className="w-3 h-3 text-violet-400 flex-shrink-0 ml-1" fill="none" stroke="currentColor" viewBox="0 0 24 24">
            <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M19 9l-7 7-7-7" />
          </svg>
        </div>
        <p className="text-xs text-violet-400">{modules.length} module{modules.length !== 1 ? 's' : ''}</p>
        <p className="text-xs text-surface-500">{promptCount}/{modules.length} prompts</p>
      </div>
      <Handle type="source" position={Position.Bottom} className="!bg-violet-400 !w-2 !h-2" />
    </>
  );
};

export default memo(GroupNode);
