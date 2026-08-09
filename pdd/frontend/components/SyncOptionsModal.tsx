/**
 * SyncOptionsModal - Modal for configuring sync options before execution.
 *
 * Used by ModuleNode, PromptSelector, PromptSpace, and ArchitectureView
 * to configure sync options (especially --agentic mode).
 */

import React, { useState, useEffect } from 'react';
import { CommandType, CommandOption } from '../types';
import { COMMANDS } from '../constants';

interface SyncOptionsModalProps {
  isOpen: boolean;
  title?: string;
  description?: string;
  onConfirm: (options: Record<string, any>) => void;
  onAddToQueue?: (options: Record<string, any>) => void;
  onClose: () => void;
}

// Helper to format option names for display
function formatOptionName(name: string): string {
  return name
    .split('-')
    .map(word => word.charAt(0).toUpperCase() + word.slice(1))
    .join(' ');
}

const SyncOptionsModal: React.FC<SyncOptionsModalProps> = ({
  isOpen,
  title = 'Sync Options',
  description = 'Configure options for running pdd sync',
  onConfirm,
  onAddToQueue,
  onClose,
}) => {
  const syncConfig = COMMANDS[CommandType.SYNC];
  const [optionValues, setOptionValues] = useState<Record<string, any>>({});

  // Initialize option values when modal opens
  useEffect(() => {
    if (isOpen) {
      const defaults: Record<string, any> = {};
      syncConfig.options.forEach(opt => {
        if (opt.defaultValue !== undefined) {
          if (opt.type === 'checkbox') {
            defaults[opt.name] = opt.defaultValue === 'true' || opt.defaultValue === true;
          } else if (opt.type === 'number') {
            defaults[opt.name] = opt.defaultValue;
          } else {
            defaults[opt.name] = opt.defaultValue;
          }
        } else if (opt.type === 'checkbox') {
          defaults[opt.name] = false;
        }
      });
      setOptionValues(defaults);
    }
  }, [isOpen, syncConfig.options]);

  const handleValueChange = (optionName: string, value: any) => {
    setOptionValues(prev => ({ ...prev, [optionName]: value }));
  };

  const handleConfirm = () => {
    onConfirm(optionValues);
    onClose();
  };

  const handleAddToQueue = () => {
    onAddToQueue?.(optionValues);
    onClose();
  };

  if (!isOpen) return null;

  return (
    <div className="fixed inset-0 bg-black/60 backdrop-blur-sm flex items-center justify-center z-50 p-4 animate-fade-in" onClick={onClose}>
      <div
        className="glass rounded-2xl border border-surface-600/50 shadow-2xl w-full max-w-sm overflow-hidden animate-scale-in"
        onClick={e => e.stopPropagation()}
      >
        {/* Header */}
        <div className="px-5 py-4 border-b border-surface-700/50">
          <div className="flex items-center gap-3">
            <div className="w-10 h-10 rounded-xl bg-gradient-to-br from-[#FDCE49] to-[#DFA84A] flex items-center justify-center">
              <svg className="w-5 h-5 text-surface-900" fill="none" stroke="currentColor" viewBox="0 0 24 24">
                <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2.5} d="M4 4v5h.582m15.356 2A8.001 8.001 0 004.582 9m0 0H9m11 11v-5h-.581m0 0a8.003 8.003 0 01-15.357-2m15.357 2H15" />
              </svg>
            </div>
            <div>
              <h3 className="text-lg font-semibold text-white">{title}</h3>
              <p className="text-xs text-surface-400">{description}</p>
            </div>
          </div>
        </div>

        {/* Options */}
        <div className="px-5 py-4 space-y-3 max-h-[60vh] overflow-y-auto">
          {syncConfig.options.map(opt => (
            <OptionInput
              key={opt.name}
              option={opt}
              value={optionValues[opt.name]}
              onChange={(val) => handleValueChange(opt.name, val)}
            />
          ))}
        </div>

        {/* Footer */}
        <div className="px-5 py-4 border-t border-surface-700/50 flex flex-col sm:flex-row justify-end gap-2 sm:gap-3">
          <button
            type="button"
            onClick={onClose}
            className="w-full sm:w-auto px-4 py-2 rounded-xl text-sm font-medium bg-surface-700/50 text-surface-300 hover:bg-surface-600 transition-colors"
          >
            Cancel
          </button>
          {onAddToQueue && (
            <button
              type="button"
              onClick={handleAddToQueue}
              className="w-full sm:w-auto px-4 py-2 rounded-xl text-sm font-medium bg-emerald-600/20 text-emerald-300 hover:bg-emerald-600 hover:text-white border border-emerald-600/30 hover:border-emerald-500/50 transition-all flex items-center justify-center gap-2"
            >
              <svg className="w-4 h-4" fill="none" stroke="currentColor" viewBox="0 0 24 24">
                <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M12 6v6m0 0v6m0-6h6m-6 0H6" />
              </svg>
              Add to Queue
            </button>
          )}
          <button
            type="button"
            onClick={handleConfirm}
            className="w-full sm:w-auto px-4 py-2 rounded-xl text-sm font-medium bg-gradient-to-r from-[#FDCE49] to-[#DFA84A] hover:from-[#FFD966] hover:to-[#FDCE49] text-surface-900 shadow-lg transition-all flex items-center justify-center gap-2"
          >
            <svg className="w-4 h-4" fill="none" stroke="currentColor" viewBox="0 0 24 24">
              <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2.5} d="M4 4v5h.582m15.356 2A8.001 8.001 0 004.582 9m0 0H9m11 11v-5h-.581m0 0a8.003 8.003 0 01-15.357-2m15.357 2H15" />
            </svg>
            Run Sync
          </button>
        </div>
      </div>
    </div>
  );
};

// Option input component
const OptionInput: React.FC<{
  option: CommandOption;
  value: any;
  onChange: (value: any) => void;
}> = ({ option, value, onChange }) => {
  const inputId = `sync-option-${option.name}`;

  if (option.type === 'checkbox') {
    return (
      <label
        htmlFor={inputId}
        className={`flex items-start gap-3 p-3 rounded-xl transition-colors cursor-pointer group ${
          value ? 'bg-accent-500/20 border border-accent-500/30' : 'bg-surface-800/30 hover:bg-surface-800/50 border border-transparent'
        }`}
      >
        <input
          type="checkbox"
          id={inputId}
          checked={!!value}
          onChange={(e) => onChange(e.target.checked)}
          className="w-4 h-4 mt-0.5 rounded bg-surface-700 border-surface-600 text-accent-500 focus:ring-accent-500 focus:ring-offset-surface-800"
        />
        <div className="flex-1 min-w-0">
          <div className={`text-sm font-medium transition-colors ${value ? 'text-accent-300' : 'text-white group-hover:text-accent-300'}`}>
            {formatOptionName(option.name)}
          </div>
          <div className="text-xs text-surface-400 mt-0.5">{option.description}</div>
        </div>
      </label>
    );
  }

  return (
    <div className="p-3 rounded-xl bg-surface-800/30 border border-transparent">
      <label htmlFor={inputId} className="block text-sm font-medium text-white mb-1.5">
        {formatOptionName(option.name)}
      </label>
      <p className="text-xs text-surface-400 mb-2">{option.description}</p>
      <input
        type={option.type === 'number' ? 'number' : 'text'}
        id={inputId}
        value={value || ''}
        onChange={(e) => onChange(option.type === 'number' ? (e.target.value ? Number(e.target.value) : '') : e.target.value)}
        placeholder={option.placeholder}
        className="w-full px-3 py-2 bg-surface-900/50 border border-surface-600 rounded-lg text-white placeholder-surface-500 focus:outline-none focus:border-accent-500 focus:ring-1 focus:ring-accent-500/50 text-sm transition-all"
      />
    </div>
  );
};

export default SyncOptionsModal;
