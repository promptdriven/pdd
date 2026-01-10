import React, { useState, useCallback } from 'react';
import { ArchitectureModule } from '../api';

interface PromptOrderModalProps {
  isOpen: boolean;
  modules: ArchitectureModule[];
  onClose: () => void;
  onConfirm: (orderedModules: ArchitectureModule[]) => void;
}

interface ModuleItem {
  module: ArchitectureModule;
  selected: boolean;
  order: number;
}

const PromptOrderModal: React.FC<PromptOrderModalProps> = ({
  isOpen,
  modules,
  onClose,
  onConfirm,
}) => {
  // Initialize with all modules selected, in original order
  const [items, setItems] = useState<ModuleItem[]>(() =>
    modules.map((module, index) => ({
      module,
      selected: true,
      order: index,
    }))
  );

  // Reset items when modules change
  React.useEffect(() => {
    setItems(
      modules.map((module, index) => ({
        module,
        selected: true,
        order: index,
      }))
    );
  }, [modules]);

  // Toggle selection
  const toggleSelection = useCallback((index: number) => {
    setItems(prev => prev.map((item, i) =>
      i === index ? { ...item, selected: !item.selected } : item
    ));
  }, []);

  // Move item up
  const moveUp = useCallback((index: number) => {
    if (index === 0) return;
    setItems(prev => {
      const newItems = [...prev];
      [newItems[index - 1], newItems[index]] = [newItems[index], newItems[index - 1]];
      return newItems;
    });
  }, []);

  // Move item down
  const moveDown = useCallback((index: number) => {
    setItems(prev => {
      if (index === prev.length - 1) return prev;
      const newItems = [...prev];
      [newItems[index], newItems[index + 1]] = [newItems[index + 1], newItems[index]];
      return newItems;
    });
  }, []);

  // Select all
  const selectAll = useCallback(() => {
    setItems(prev => prev.map(item => ({ ...item, selected: true })));
  }, []);

  // Deselect all
  const deselectAll = useCallback(() => {
    setItems(prev => prev.map(item => ({ ...item, selected: false })));
  }, []);

  // Handle confirm
  const handleConfirm = useCallback(() => {
    const selectedModules = items
      .filter(item => item.selected)
      .map(item => item.module);
    onConfirm(selectedModules);
  }, [items, onConfirm]);

  // Get module display name
  const getModuleName = (module: ArchitectureModule): string => {
    return module.filename.replace(/_[A-Za-z]+\.prompt$/, '').replace(/\.prompt$/, '');
  };

  // Get language from filename
  const getLanguage = (module: ArchitectureModule): string => {
    const match = module.filename.match(/_([A-Za-z]+)\.prompt$/);
    return match?.[1] || 'Unknown';
  };

  const selectedCount = items.filter(i => i.selected).length;

  if (!isOpen) return null;

  return (
    <div className="fixed inset-0 z-50 flex items-center justify-center">
      {/* Backdrop */}
      <div
        className="absolute inset-0 bg-black/60 backdrop-blur-sm"
        onClick={onClose}
      />

      {/* Modal */}
      <div className="relative bg-surface-900 rounded-2xl border border-surface-700 shadow-2xl w-full max-w-lg max-h-[80vh] flex flex-col">
        {/* Header */}
        <div className="p-4 border-b border-surface-700">
          <h2 className="text-lg font-semibold text-white">Configure Prompt Generation</h2>
          <p className="text-sm text-surface-400 mt-1">
            Select modules and set the generation order. Prompts will be generated from top to bottom.
          </p>
        </div>

        {/* Toolbar */}
        <div className="px-4 py-2 border-b border-surface-700/50 flex items-center justify-between">
          <div className="flex items-center gap-2">
            <button
              onClick={selectAll}
              className="px-2 py-1 text-xs text-surface-300 hover:text-white hover:bg-surface-700 rounded transition-colors"
            >
              Select All
            </button>
            <button
              onClick={deselectAll}
              className="px-2 py-1 text-xs text-surface-300 hover:text-white hover:bg-surface-700 rounded transition-colors"
            >
              Deselect All
            </button>
          </div>
          <span className="text-xs text-surface-400">
            {selectedCount} of {items.length} selected
          </span>
        </div>

        {/* Module List */}
        <div className="flex-1 overflow-y-auto p-2">
          <div className="space-y-1">
            {items.map((item, index) => (
              <div
                key={item.module.filename}
                className={`flex items-center gap-2 p-2 rounded-lg border transition-colors ${
                  item.selected
                    ? 'bg-surface-800 border-surface-600'
                    : 'bg-surface-800/30 border-surface-700/30 opacity-60'
                }`}
              >
                {/* Checkbox */}
                <input
                  type="checkbox"
                  checked={item.selected}
                  onChange={() => toggleSelection(index)}
                  className="w-4 h-4 rounded border-surface-600 bg-surface-700 text-accent-500 focus:ring-accent-500 cursor-pointer"
                />

                {/* Order number */}
                <span className="w-6 text-center text-xs font-mono text-surface-500">
                  {item.selected ? items.filter((it, i) => i <= index && it.selected).length : '-'}
                </span>

                {/* Module info */}
                <div className="flex-1 min-w-0">
                  <div className="flex items-center gap-2">
                    <span className="font-medium text-sm text-white truncate">
                      {getModuleName(item.module)}
                    </span>
                    <span className="px-1.5 py-0.5 text-[10px] font-medium bg-surface-700 text-surface-300 rounded">
                      {getLanguage(item.module)}
                    </span>
                  </div>
                  <p className="text-xs text-surface-500 truncate">
                    {item.module.description?.substring(0, 60) || item.module.filepath}
                    {(item.module.description?.length || 0) > 60 ? '...' : ''}
                  </p>
                </div>

                {/* Priority badge */}
                <span className={`px-1.5 py-0.5 text-[10px] font-medium rounded ${
                  item.module.priority === 'high'
                    ? 'bg-red-500/20 text-red-300'
                    : item.module.priority === 'medium'
                    ? 'bg-yellow-500/20 text-yellow-300'
                    : 'bg-green-500/20 text-green-300'
                }`}>
                  {item.module.priority || 'normal'}
                </span>

                {/* Move buttons */}
                <div className="flex flex-col gap-0.5">
                  <button
                    onClick={() => moveUp(index)}
                    disabled={index === 0}
                    className="p-1 hover:bg-surface-600 rounded disabled:opacity-30 disabled:cursor-not-allowed transition-colors"
                    title="Move up"
                  >
                    <svg className="w-3 h-3 text-surface-400" fill="none" stroke="currentColor" viewBox="0 0 24 24">
                      <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M5 15l7-7 7 7" />
                    </svg>
                  </button>
                  <button
                    onClick={() => moveDown(index)}
                    disabled={index === items.length - 1}
                    className="p-1 hover:bg-surface-600 rounded disabled:opacity-30 disabled:cursor-not-allowed transition-colors"
                    title="Move down"
                  >
                    <svg className="w-3 h-3 text-surface-400" fill="none" stroke="currentColor" viewBox="0 0 24 24">
                      <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M19 9l-7 7-7-7" />
                    </svg>
                  </button>
                </div>
              </div>
            ))}
          </div>
        </div>

        {/* Footer */}
        <div className="p-4 border-t border-surface-700 flex items-center justify-between">
          <p className="text-xs text-surface-500">
            Dependencies are not automatically resolved. Ensure correct order.
          </p>
          <div className="flex items-center gap-2">
            <button
              onClick={onClose}
              className="px-4 py-2 text-sm font-medium text-surface-300 hover:text-white hover:bg-surface-700 rounded-lg transition-colors"
            >
              Cancel
            </button>
            <button
              onClick={handleConfirm}
              disabled={selectedCount === 0}
              className={`px-4 py-2 text-sm font-medium rounded-lg transition-colors ${
                selectedCount === 0
                  ? 'bg-surface-700 text-surface-500 cursor-not-allowed'
                  : 'bg-emerald-600 text-white hover:bg-emerald-500'
              }`}
            >
              Generate {selectedCount} Prompt{selectedCount !== 1 ? 's' : ''}
            </button>
          </div>
        </div>
      </div>
    </div>
  );
};

export default PromptOrderModal;
