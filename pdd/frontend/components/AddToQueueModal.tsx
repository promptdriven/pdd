/**
 * AddToQueueModal - Modal for adding tasks to the queue without immediate execution.
 *
 * Similar to CommandOptionsModal but adds to queue instead of running immediately.
 */

import React, { useState, useMemo } from 'react';
import { PromptInfo } from '../api';
import { CommandType, CommandConfig, CommandOption, GlobalOption } from '../types';
import { COMMANDS, GLOBAL_OPTIONS } from '../constants';
import { buildDisplayCommand } from '../lib/commandBuilder';
import FilePickerInput from './FilePickerInput';

interface AddToQueueModalProps {
  isOpen: boolean;
  prompt: PromptInfo | null;
  preselectedCommand?: CommandType;
  onAddToQueue: (
    commandType: CommandType,
    prompt: PromptInfo,
    rawOptions: Record<string, any>,
    displayCommand: string
  ) => void;
  onClose: () => void;
}

// Helper to format option names for display
function formatOptionName(name: string): string {
  return name
    .split('-')
    .map(word => word.charAt(0).toUpperCase() + word.slice(1))
    .join(' ');
}

// Option input component
const OptionInput: React.FC<{
  option: CommandOption | GlobalOption;
  value: any;
  onChange: (value: any) => void;
  compact?: boolean;
}> = ({ option, value, onChange, compact = false }) => {
  const inputId = `queue-option-${option.name}`;

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
            className="flex-1 h-2 bg-surface-700 rounded-full appearance-none cursor-pointer accent-accent-500"
          />
          <span className="text-[10px] text-surface-500 w-6">{max}</span>
        </div>
      </div>
    );
  }

  return (
    <div>
      <label htmlFor={inputId} className={`block ${compact ? 'text-xs' : 'text-sm'} font-medium text-white mb-1.5`}>
        {formatOptionName(option.name)}
        {option.required && <span className="text-red-400 ml-1">*</span>}
      </label>
      <p className={`${compact ? 'text-[10px]' : 'text-xs'} text-surface-400 mb-2`}>{option.description}</p>
      <input
        type={option.type === 'number' ? 'number' : 'text'}
        id={inputId}
        value={value || ''}
        onChange={(e) => onChange(option.type === 'number' ? (e.target.value ? Number(e.target.value) : '') : e.target.value)}
        placeholder={option.placeholder}
        required={option.required}
        className="w-full px-3 py-2.5 bg-surface-900/50 border border-surface-600 rounded-xl text-white placeholder-surface-500 focus:outline-none focus:border-accent-500 focus:ring-1 focus:ring-accent-500/50 text-sm transition-all"
      />
    </div>
  );
};

const AddToQueueModal: React.FC<AddToQueueModalProps> = ({
  isOpen,
  prompt,
  preselectedCommand,
  onAddToQueue,
  onClose,
}) => {
  // Get available commands that require a prompt
  const availableCommands = useMemo(() =>
    Object.values(COMMANDS).filter(cmd => cmd.requiresPrompt),
    []
  );

  const [selectedCommand, setSelectedCommand] = useState<CommandType | null>(preselectedCommand || null);
  const [showAdvanced, setShowAdvanced] = useState(false);
  const [optionValues, setOptionValues] = useState<Record<string, any>>({});

  // Get config for selected command
  const commandConfig = selectedCommand ? COMMANDS[selectedCommand] : null;

  // Initialize option values when command changes
  React.useEffect(() => {
    if (!commandConfig) {
      setOptionValues({});
      return;
    }

    const defaults: Record<string, any> = {};

    // Set defaults from command options
    commandConfig.options.forEach(opt => {
      if (opt.defaultValue !== undefined) {
        if (opt.type === 'checkbox') {
          defaults[opt.name] = opt.defaultValue === 'true' || opt.defaultValue === true;
        } else if (opt.type === 'number' || opt.type === 'range') {
          defaults[opt.name] = opt.defaultValue;
        } else {
          defaults[opt.name] = opt.defaultValue;
        }
      }
    });

    // Pre-fill file paths from detected files
    if (commandConfig.requiresCode && prompt?.code) {
      defaults['_code'] = prompt.code;
    }
    if (commandConfig.requiresTest && prompt?.test) {
      defaults['_test'] = prompt.test;
    }

    // Special case: for Submit Example, pre-fill verification-program with example file
    if (commandConfig.name === CommandType.SUBMIT_EXAMPLE && prompt?.example) {
      defaults['verification-program'] = prompt.example;
    }

    // Set global option defaults
    GLOBAL_OPTIONS.forEach(opt => {
      defaults[`_global_${opt.name}`] = opt.defaultValue;
    });

    setOptionValues(defaults);
  }, [commandConfig, prompt]);

  // Reset when modal closes
  React.useEffect(() => {
    if (!isOpen) {
      setSelectedCommand(preselectedCommand || null);
      setShowAdvanced(false);
    }
  }, [isOpen, preselectedCommand]);

  const handleValueChange = (optionName: string, value: any) => {
    setOptionValues(prev => ({ ...prev, [optionName]: value }));
  };

  const handleAddToQueue = () => {
    if (!commandConfig || !prompt || !selectedCommand) return;

    // Store the raw inputs (commandType, prompt, rawOptions) so the command
    // can be reconstructed exactly like PromptSpace at execution time.
    // This ensures queue execution uses the same code path as direct execution.
    const display = buildDisplayCommand(commandConfig.name, prompt, optionValues);

    onAddToQueue(commandConfig.name, prompt, optionValues, display);
    onClose();
  };

  // Check if any global options differ from defaults
  const hasCustomGlobalOptions = GLOBAL_OPTIONS.some(opt => {
    const value = optionValues[`_global_${opt.name}`];
    return value !== opt.defaultValue;
  });

  if (!isOpen) return null;

  // Safety check - ensure we have valid data before rendering
  if (!Array.isArray(availableCommands)) {
    console.error('AddToQueueModal: availableCommands is not an array');
    return null;
  }

  return (
    <div className="fixed inset-0 bg-black/60 backdrop-blur-sm flex items-center justify-center z-50 p-4 animate-fade-in" onClick={onClose}>
      <div
        className="glass rounded-none sm:rounded-2xl border-0 sm:border border-surface-600/50 shadow-2xl w-full h-full sm:h-auto sm:max-w-md sm:max-h-[90vh] overflow-y-auto animate-scale-in"
        onClick={e => e.stopPropagation()}
      >
        <div className="px-4 sm:px-6 py-4 border-b border-surface-700/50">
          <div className="flex items-center gap-3">
            <div className="w-10 h-10 rounded-xl bg-emerald-500/20 flex items-center justify-center">
              <svg className="w-5 h-5 text-emerald-400" fill="none" stroke="currentColor" viewBox="0 0 24 24">
                <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M12 6v6m0 0v6m0-6h6m-6 0H6" />
              </svg>
            </div>
            <div>
              <h3 className="text-lg font-semibold text-white">Add to Task Queue</h3>
              <p className="text-xs sm:text-sm text-surface-400">Queue this task for later execution</p>
            </div>
          </div>
        </div>

        <div className="px-4 sm:px-6 py-4 space-y-4 max-h-[50vh] sm:max-h-[60vh] overflow-y-auto">
          {/* Prompt info */}
          {prompt && (
            <div className="bg-surface-800/50 rounded-xl px-3 py-2.5 border border-surface-700/50">
              <div className="text-xs text-surface-400 mb-0.5">Target Prompt</div>
              <div className="text-sm text-white font-mono truncate">{prompt.sync_basename || prompt.prompt?.split('/').pop() || 'Unknown'}</div>
            </div>
          )}

          {/* Command selector */}
          <div>
            <label className="block text-sm font-medium text-white mb-2">Command</label>
            <div className="grid grid-cols-2 gap-2">
              {availableCommands.map(cmd => cmd && (
                <button
                  key={cmd.name}
                  onClick={() => setSelectedCommand(cmd.name)}
                  className={`
                    flex items-center gap-2 px-3 py-2.5 rounded-xl text-sm text-left transition-all
                    ${selectedCommand === cmd.name
                      ? 'bg-accent-600 text-white border border-accent-500'
                      : 'bg-surface-800/50 text-surface-300 border border-surface-700 hover:bg-surface-700/50'
                    }
                  `}
                >
                  <span>{cmd.icon || '▶'}</span>
                  <span className="truncate">{cmd.shortDescription || cmd.name}</span>
                </button>
              ))}
            </div>
          </div>

          {/* Command options (when command selected) */}
          {commandConfig && (
            <>
              {/* File path inputs for required files */}
              {commandConfig.requiresCode && (
                <FilePickerInput
                  label="Code File"
                  value={optionValues['_code'] || ''}
                  onChange={(path) => handleValueChange('_code', path)}
                  placeholder="e.g., src/calculator.py"
                  required
                  filter={['.py', '.ts', '.tsx', '.js', '.jsx', '.java', '.go', '.rs', '.rb', '.php', '.cs', '.cpp', '.c', '.h']}
                  title="Select Code File"
                  isDetected={!!prompt?.code}
                />
              )}

              {commandConfig.requiresTest && (
                <FilePickerInput
                  label="Test File"
                  value={optionValues['_test'] || ''}
                  onChange={(path) => handleValueChange('_test', path)}
                  placeholder="e.g., tests/test_calculator.py"
                  required
                  filter={['.py', '.ts', '.tsx', '.js', '.jsx', '.java', '.go', '.rs', '.rb', '.php', '.cs', '.cpp', '.c']}
                  title="Select Test File"
                  isDetected={!!prompt?.test}
                />
              )}

              {/* Command-specific options */}
              {commandConfig.options.length > 0 && (
                <div className="space-y-3">
                  {commandConfig.options.map(opt => (
                    <OptionInput
                      key={opt.name}
                      option={opt}
                      value={optionValues[opt.name]}
                      onChange={(val) => handleValueChange(opt.name, val)}
                    />
                  ))}
                </div>
              )}

              {/* Advanced Options (Global) - Collapsible */}
              <div className="border-t border-surface-700/30 pt-3 mt-2">
                <button
                  type="button"
                  onClick={() => setShowAdvanced(!showAdvanced)}
                  className="w-full flex items-center justify-between text-left group"
                >
                  <div className="flex items-center gap-2">
                    <span className="text-xs font-semibold text-surface-400 uppercase tracking-wider">
                      Advanced Options
                    </span>
                    {hasCustomGlobalOptions && (
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
                  <div className="mt-3 space-y-3 animate-slide-down">
                    {/* Model Settings Group */}
                    <div className="space-y-3 p-3 rounded-xl bg-surface-800/20 border border-surface-700/30">
                      <div className="text-[10px] font-medium text-surface-500 uppercase tracking-wider">Model Settings</div>
                      {GLOBAL_OPTIONS.filter(opt => ['strength', 'temperature', 'time'].includes(opt.name)).map(opt => (
                        <OptionInput
                          key={opt.name}
                          option={opt}
                          value={optionValues[`_global_${opt.name}`]}
                          onChange={(val) => handleValueChange(`_global_${opt.name}`, val)}
                          compact
                        />
                      ))}
                    </div>

                    {/* Execution Options Group */}
                    <div className="space-y-1 p-3 rounded-xl bg-surface-800/20 border border-surface-700/30">
                      <div className="text-[10px] font-medium text-surface-500 uppercase tracking-wider mb-2">Execution Options</div>
                      {GLOBAL_OPTIONS.filter(opt => ['local', 'verbose', 'quiet', 'force', 'review-examples'].includes(opt.name)).map(opt => (
                        <OptionInput
                          key={opt.name}
                          option={opt}
                          value={optionValues[`_global_${opt.name}`]}
                          onChange={(val) => handleValueChange(`_global_${opt.name}`, val)}
                          compact
                        />
                      ))}
                    </div>
                  </div>
                )}
              </div>
            </>
          )}
        </div>

        <div className="px-4 sm:px-6 py-4 border-t border-surface-700/50 flex flex-col-reverse sm:flex-row justify-end gap-2 sm:gap-3">
          <button
            type="button"
            onClick={onClose}
            className="w-full sm:w-auto px-4 py-2.5 rounded-xl text-sm font-medium bg-surface-700/50 text-surface-300 hover:bg-surface-600 transition-colors"
          >
            Cancel
          </button>
          <button
            type="button"
            onClick={handleAddToQueue}
            disabled={!selectedCommand || !prompt}
            className="w-full sm:w-auto px-4 py-2.5 rounded-xl text-sm font-medium bg-gradient-to-r from-emerald-600 to-emerald-500 hover:from-emerald-500 hover:to-emerald-400 text-white shadow-lg shadow-emerald-500/25 transition-all flex items-center justify-center gap-2 disabled:opacity-50 disabled:cursor-not-allowed"
          >
            <svg className="w-4 h-4" fill="none" stroke="currentColor" viewBox="0 0 24 24">
              <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M12 6v6m0 0v6m0-6h6m-6 0H6" />
            </svg>
            <span>Add to Queue</span>
          </button>
        </div>
      </div>
    </div>
  );
};

export default AddToQueueModal;
