import React, { useState, useEffect } from 'react';
import { api, FileTreeNode } from '../api';
import { ChevronDownIcon, ChevronUpIcon, FolderIcon, DocumentTextIcon, CodeBracketIcon, ClipboardDocumentListIcon, DocumentIcon } from './Icon';

interface FileBrowserProps {
  onSelect: (path: string) => void;
  onClose?: () => void;  // For modal mode - called when clicking outside or pressing escape
  filter?: string | string[];  // File extensions to show, e.g., '.md' or ['.prompt', '.py']
  title?: string;
  directoryMode?: boolean;  // If true, only allow selecting directories
}

interface TreeNodeProps {
  node: FileTreeNode;
  onSelect: (path: string) => void;
  filter?: string[];  // Normalized to array internally
  depth: number;
  directoryMode?: boolean;  // If true, directories are selectable
}

const FileIcon = ({ type, name }: { type: 'file' | 'directory'; name: string }) => {
  if (type === 'directory') {
    return <FolderIcon className="w-4 h-4 text-surface-400 mr-2 flex-shrink-0" />;
  }

  // File type icons - all using muted surface-400 color for non-distracting appearance
  if (name.endsWith('.prompt')) return <DocumentTextIcon className="w-4 h-4 text-surface-400 mr-2 flex-shrink-0" />;
  if (name.endsWith('.py')) return <CodeBracketIcon className="w-4 h-4 text-surface-400 mr-2 flex-shrink-0" />;
  if (name.endsWith('.ts') || name.endsWith('.tsx')) return <CodeBracketIcon className="w-4 h-4 text-surface-400 mr-2 flex-shrink-0" />;
  if (name.endsWith('.js') || name.endsWith('.jsx')) return <CodeBracketIcon className="w-4 h-4 text-surface-400 mr-2 flex-shrink-0" />;
  if (name.endsWith('.json')) return <ClipboardDocumentListIcon className="w-4 h-4 text-surface-400 mr-2 flex-shrink-0" />;
  if (name.endsWith('.md')) return <DocumentIcon className="w-4 h-4 text-surface-400 mr-2 flex-shrink-0" />;

  return <DocumentIcon className="w-4 h-4 text-surface-400 mr-2 flex-shrink-0" />;
};

const TreeNode: React.FC<TreeNodeProps> = ({ node, onSelect, filter, depth, directoryMode }) => {
  const [isExpanded, setIsExpanded] = useState(depth < 2);

  const isDirectory = node.type === 'directory';

  // Filter check for files
  const shouldShow = () => {
    if (isDirectory) return true;
    // In directory mode, don't show files
    if (directoryMode) return false;
    if (!filter || filter.length === 0) return true;
    return filter.some(ext => node.name.endsWith(ext));
  };

  if (!shouldShow()) return null;

  // For directories, check if any children would be visible
  const visibleChildren = node.children?.filter(child => {
    if (child.type === 'directory') return true;
    // In directory mode, don't show files
    if (directoryMode) return false;
    if (!filter || filter.length === 0) return true;
    return filter.some(ext => child.name.endsWith(ext));
  }) || [];

  // Hide empty directories when filtering (but not in directory mode)
  if (isDirectory && !directoryMode && filter && filter.length > 0 && visibleChildren.length === 0) {
    return null;
  }

  const handleClick = () => {
    if (isDirectory) {
      setIsExpanded(!isExpanded);
    } else {
      onSelect(node.path);
    }
  };

  const handleSelectDirectory = (e: React.MouseEvent) => {
    e.stopPropagation();
    onSelect(node.path);
  };

  return (
    <div>
      <div
        className={`flex items-center py-1 px-2 cursor-pointer rounded transition-colors ${
          isDirectory ? 'hover:bg-surface-700' : 'hover:bg-accent-600/20'
        }`}
        style={{ paddingLeft: `${depth * 16 + 8}px` }}
        onClick={handleClick}
      >
        {isDirectory && (
          <span className="mr-1 text-surface-400">
            {isExpanded ? (
              <ChevronDownIcon className="w-4 h-4" />
            ) : (
              <ChevronUpIcon className="w-4 h-4 rotate-90" />
            )}
          </span>
        )}
        <FileIcon type={node.type} name={node.name} />
        <span className={`text-sm flex-1 ${isDirectory ? 'text-surface-200' : 'text-surface-300'}`}>
          {node.name}
        </span>
        {directoryMode && isDirectory && (
          <button
            onClick={handleSelectDirectory}
            className="ml-2 px-2 py-0.5 text-xs bg-accent-600/20 hover:bg-accent-600/40 text-accent-400 rounded transition-colors"
          >
            Select
          </button>
        )}
      </div>

      {isDirectory && isExpanded && visibleChildren.map((child, i) => (
        <TreeNode
          key={child.path || i}
          node={child}
          onSelect={onSelect}
          filter={filter}
          depth={depth + 1}
          directoryMode={directoryMode}
        />
      ))}
    </div>
  );
};

const FileBrowser: React.FC<FileBrowserProps> = ({ onSelect, onClose, filter, title = 'Select File', directoryMode = false }) => {
  const [tree, setTree] = useState<FileTreeNode | null>(null);
  const [loading, setLoading] = useState(true);
  const [error, setError] = useState<string | null>(null);
  const [searchQuery, setSearchQuery] = useState('');

  // Normalize filter to array
  const normalizedFilter = filter
    ? (Array.isArray(filter) ? filter : [filter])
    : undefined;

  useEffect(() => {
    loadTree();
  }, []);

  const loadTree = async () => {
    setLoading(true);
    setError(null);
    try {
      const data = await api.getFileTree('', 5);
      setTree(data);
    } catch (e: any) {
      setError(e.message || 'Failed to load file tree');
    } finally {
      setLoading(false);
    }
  };

  const handleSelect = (path: string) => {
    onSelect(path);
  };

  const content = loading ? (
    <div className="bg-surface-800 rounded-lg p-4 border border-surface-700">
      <div className="text-surface-400 text-center">Loading files...</div>
    </div>
  ) : error ? (
    <div className="bg-surface-800 rounded-lg p-4 border border-surface-700">
      <div className="text-red-400 text-center">{error}</div>
      <button
        onClick={loadTree}
        className="mt-2 w-full py-1 bg-surface-700 hover:bg-surface-600 rounded text-sm"
      >
        Retry
      </button>
    </div>
  ) : (
    <div className="bg-surface-800 rounded-lg border border-surface-700 overflow-hidden">
      <div className="p-3 border-b border-surface-700 flex items-center justify-between">
        <h3 className="text-sm font-medium text-surface-200">{title}</h3>
        {onClose && (
          <button
            onClick={onClose}
            className="p-1 hover:bg-surface-700 rounded text-surface-400 hover:text-white transition-colors"
          >
            <svg className="w-4 h-4" fill="none" stroke="currentColor" viewBox="0 0 24 24">
              <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M6 18L18 6M6 6l12 12" />
            </svg>
          </button>
        )}
      </div>
      <div className="p-3 border-b border-surface-700/50">
        <input
          type="text"
          placeholder="Search files..."
          value={searchQuery}
          onChange={(e) => setSearchQuery(e.target.value)}
          className="w-full px-3 py-1.5 bg-surface-900 border border-surface-600 rounded text-sm text-surface-200 placeholder-surface-500 focus:outline-none focus:border-accent-500"
        />
        {directoryMode ? (
          <div className="mt-2 text-xs text-surface-500">
            Showing directories only
          </div>
        ) : normalizedFilter && normalizedFilter.length > 0 ? (
          <div className="mt-2 text-xs text-surface-500">
            Showing: {normalizedFilter.join(', ')}
          </div>
        ) : null}
      </div>

      <div className="max-h-80 overflow-y-auto p-2">
        {tree ? (
          <TreeNode
            node={tree}
            onSelect={handleSelect}
            filter={normalizedFilter}
            depth={0}
            directoryMode={directoryMode}
          />
        ) : (
          <div className="text-surface-500 text-center py-4">No files found</div>
        )}
      </div>
    </div>
  );

  // If onClose is provided, render as a modal
  if (onClose) {
    return (
      <div
        className="fixed inset-0 bg-black/60 flex items-center justify-center z-50"
        onClick={(e) => {
          if (e.target === e.currentTarget) onClose();
        }}
      >
        <div className="w-full max-w-md mx-4">
          {content}
        </div>
      </div>
    );
  }

  return content;
};

export default FileBrowser;
