import React, { useState, useCallback } from 'react';
import { ArchitectureModule, GenerationGlobalOptions } from '../api';
import { GLOBAL_OPTIONS, GLOBAL_DEFAULTS } from '../constants';
import { GlobalOption, CommandOption } from '../types';

// Helper to format option names for display
function formatOptionName(name: string): string {
  return name
    .split('-')
    .map(word => word.charAt(0).toUpperCase() + word.slice(1))
    .join(' ');
}

// Individual option input component
const OptionInput: React.FC<{
  option: CommandOption | GlobalOption;
  value: any;
  onChange: (value: any) => void;
  compact?: boolean;
}> = ({ option, value, onChange, compact = false }) => {
  const inputId = `modal-option-${option.name}`;

  if (option.type === 'checkbox') {
    return (
      <label htmlFor={inputId} className={`flex items-start gap-3 ${compact ? 'p-2' : 'p-3'} rounded-xl bg-surface-800/30 hover:bg-surface-800/50 transition-colors cursor-pointer group`}>
        <input
          type="checkbox"
          id={inputId}
          checked={!!value}
          onChange={(e) => onChange(e.target.checked)}
          className="w-4 h-4 mt-0.5 rounded bg-surface-700 border-surface-600 text-accent-500 focus:ring-accent-500 focus:ring-offset-surface-800"
        />
        <div className="flex-1 min-w-0">
          <div className={`${compact ? 'text-xs' : 'text-sm'} font-medium text-white group-hover:text-accent-300 transition-colors`}>{formatOptionName(option.name)}</div>
          <div className={`${compact ? 'text-[10px]' : 'text-xs'} text-surface-400 mt-0.5`}>{option.description}</div>
        </div>
      </label>
    );
  }

  if (option.type === 'range') {
    const min = option.min ?? 0;
    const max = option.max ?? 1;
    const step = option.step ?? 0.1;
    const displayValue = value ?? option.defaultValue ?? min;

    return (
      <div className={compact ? 'space-y-1.5' : 'space-y-2'}>
        <div className="flex items-center justify-between">
          <label htmlFor={inputId} className={`${compact ? 'text-xs' : 'text-sm'} font-medium text-white`}>
            {formatOptionName(option.name)}
          </label>
          <span className={`${compact ? 'text-xs' : 'text-sm'} font-mono text-accent-400 bg-accent-500/10 px-2 py-0.5 rounded-lg`}>
            {typeof displayValue === 'number' ? displayValue.toFixed(2) : displayValue}
          </span>
        </div>
        <p className={`${compact ? 'text-[10px]' : 'text-xs'} text-surface-400`}>{option.description}</p>
        <div className="flex items-center gap-3">
          <span className="text-[10px] text-surface-500 w-6 text-right">{min}</span>
          <input
            type="range"
            id={inputId}
            min={min}
            max={max}
            step={step}
            value={displayValue}
            onChange={(e) => onChange(parseFloat(e.target.value))}
            className="flex-1 h-2 bg-surface-700 rounded-full appearance-none cursor-pointer accent-accent-500
              [&::-webkit-slider-thumb]:appearance-none [&::-webkit-slider-thumb]:w-4 [&::-webkit-slider-thumb]:h-4
              [&::-webkit-slider-thumb]:rounded-full [&::-webkit-slider-thumb]:bg-accent-500
              [&::-webkit-slider-thumb]:shadow-lg [&::-webkit-slider-thumb]:shadow-accent-500/30
              [&::-webkit-slider-thumb]:hover:bg-accent-400 [&::-webkit-slider-thumb]:transition-colors"
          />
          <span className="text-[10px] text-surface-500 w-6">{max}</span>
        </div>
      </div>
    );
  }

  return null;
};

interface PromptOrderModalProps {
  isOpen: boolean;
  modules: ArchitectureModule[];
  existingPrompts?: Set<string>;
  globalOptions: GenerationGlobalOptions;
  onGlobalOptionsChange: (options: GenerationGlobalOptions) => void;
  onClose: () => void;
  onConfirm: (orderedModules: ArchitectureModule[]) => void;
}

interface ModuleItem {
  module: ArchitectureModule;
  selected: boolean;
  order: number;
  hasExistingPrompt: boolean;
}

const PromptOrderModal: React.FC<PromptOrderModalProps> = ({
  isOpen,
  modules,
  existingPrompts = new Set(),
  globalOptions,
  onGlobalOptionsChange,
  onClose,
  onConfirm,
}) => {
  const [showAdvanced, setShowAdvanced] = useState(false);
  // Initialize with only modules without existing prompts selected
  const [items, setItems] = useState<ModuleItem[]>(() =>
    modules.map((module, index) => {
      const hasExisting = existingPrompts.has(module.filename);
      return {
        module,
        selected: !hasExisting,  // Only select modules without existing prompts
        order: index,
        hasExistingPrompt: hasExisting,
      };
    })
  );

  // Reset items when modules or existingPrompts change
  React.useEffect(() => {
    setItems(
      modules.map((module, index) => {
        const hasExisting = existingPrompts.has(module.filename);
        return {
          module,
          selected: !hasExisting,  // Only select modules without existing prompts
          order: index,
          hasExistingPrompt: hasExisting,
        };
      })
    );
  }, [modules, existingPrompts]);

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

  // Select only missing prompts (modules without existing prompts)
  const selectOnlyMissing = useCallback(() => {
    setItems(prev => prev.map(item => ({ ...item, selected: !item.hasExistingPrompt })));
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
              onClick={selectOnlyMissing}
              className="px-2 py-1 text-xs text-emerald-400 hover:text-emerald-300 hover:bg-emerald-500/10 rounded transition-colors font-medium"
            >
              Select Missing
            </button>
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
                } ${item.hasExistingPrompt ? 'ring-1 ring-emerald-500/30' : ''}`}
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
                    {/* Existing prompt indicator */}
                    {item.hasExistingPrompt && (
                      <span className="flex items-center gap-1 px-1.5 py-0.5 text-[10px] font-medium bg-emerald-500/20 text-emerald-400 rounded">
                        <svg className="w-2.5 h-2.5" fill="none" stroke="currentColor" viewBox="0 0 24 24">
                          <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M5 13l4 4L19 7" />
                        </svg>
                        exists
                      </span>
                    )}
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

        {/* Advanced Options */}
        <div className="border-t border-surface-700/50">
          <button
            type="button"
            onClick={() => setShowAdvanced(!showAdvanced)}
            className="w-full px-4 py-3 flex items-center justify-between text-left hover:bg-surface-800/30 transition-colors"
          >
            <div className="flex items-center gap-2">
              <span className="text-xs font-semibold text-surface-400 uppercase tracking-wider">
                Advanced Options
              </span>
              {(globalOptions.strength !== GLOBAL_DEFAULTS.strength ||
                globalOptions.temperature !== GLOBAL_DEFAULTS.temperature ||
                globalOptions.time !== GLOBAL_DEFAULTS.time ||
                globalOptions.local ||
                globalOptions.verbose ||
                globalOptions.quiet ||
                globalOptions.force) && (
                <span className="w-2 h-2 rounded-full bg-accent-500 animate-pulse" title="Custom settings applied" />
              )}
            </div>
            <svg
              className={`w-4 h-4 text-surface-400 transition-transform duration-200 ${showAdvanced ? 'rotate-180' : ''}`}
              fill="none"
              stroke="currentColor"
              viewBox="0 0 24 24"
            >
              <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M19 9l-7 7-7-7" />
            </svg>
          </button>

          {showAdvanced && (
            <div className="px-4 pb-4 space-y-3">
              {/* Model Settings Group */}
              <div className="space-y-3 p-3 rounded-xl bg-surface-800/20 border border-surface-700/30">
                <div className="text-[10px] font-medium text-surface-500 uppercase tracking-wider">Model Settings</div>
                {GLOBAL_OPTIONS.filter(opt => ['strength', 'temperature', 'time'].includes(opt.name)).map(opt => (
                  <OptionInput
                    key={opt.name}
                    option={opt}
                    value={globalOptions[opt.name as keyof GenerationGlobalOptions]}
                    onChange={(val) => onGlobalOptionsChange({ ...globalOptions, [opt.name]: val })}
                    compact
                  />
                ))}
              </div>

              {/* Execution Options Group */}
              <div className="space-y-1 p-3 rounded-xl bg-surface-800/20 border border-surface-700/30">
                <div className="text-[10px] font-medium text-surface-500 uppercase tracking-wider mb-2">Execution Options</div>
                {GLOBAL_OPTIONS.filter(opt => ['local', 'verbose', 'quiet', 'force'].includes(opt.name)).map(opt => (
                  <OptionInput
                    key={opt.name}
                    option={opt}
                    value={globalOptions[opt.name as keyof GenerationGlobalOptions]}
                    onChange={(val) => onGlobalOptionsChange({ ...globalOptions, [opt.name]: val })}
                    compact
                  />
                ))}
              </div>
            </div>
          )}
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
