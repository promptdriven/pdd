/**
 * AddToQueueModal - Modal for adding tasks to the queue without immediate execution.
 *
 * Similar to CommandOptionsModal but adds to queue instead of running immediately.
 */

import React, { useState, useMemo } from 'react';
import { PromptInfo, CommandRequest } from '../api';
import { CommandType, CommandConfig, CommandOption, GlobalOption } from '../types';
import { COMMANDS, GLOBAL_OPTIONS } from '../constants';

interface AddToQueueModalProps {
  isOpen: boolean;
  prompt: PromptInfo | null;
  preselectedCommand?: CommandType;
  onAddToQueue: (
    command: string,
    prompt: PromptInfo | null,
    request: CommandRequest,
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

  const buildCommandRequest = (): { request: CommandRequest; displayCommand: string } | null => {
    if (!commandConfig || !prompt) return null;

    const command = commandConfig.name;
    const codeFile = optionValues['_code'] || prompt.code;
    const testFile = optionValues['_test'] || prompt.test;

    // Build clean options for CLI
    const options: Record<string, any> = {};

    // Add command-specific options (remove internal prefixes)
    commandConfig.options.forEach(opt => {
      const value = optionValues[opt.name];
      if (value !== '' && value !== undefined && value !== null && value !== opt.defaultValue) {
        options[opt.name] = value;
      }
    });

    // Add global options (strip _global_ prefix)
    GLOBAL_OPTIONS.forEach(opt => {
      const value = optionValues[`_global_${opt.name}`];
      if (value !== opt.defaultValue && value !== undefined && value !== null) {
        options[opt.name] = value;
      }
    });

    // Build args based on command type (matching handleRunCommand in App.tsx exactly)
    const args: Record<string, any> = {};

    if (command === CommandType.SYNC) {
      // Sync uses basename, not prompt_file
      args.basename = prompt.sync_basename;
      if (prompt.context) {
        options['context'] = prompt.context;
      }
    } else if (command === CommandType.UPDATE) {
      // Update command: pdd update [PROMPT_FILE] <CODE_FILE> [ORIGINAL_CODE_FILE]
      if (codeFile) {
        args.args = [prompt.prompt, codeFile];
      } else {
        args.args = [];
      }
    } else if (command === CommandType.GENERATE) {
      args.prompt_file = prompt.prompt;
    } else if (command === CommandType.TEST) {
      args.prompt_file = prompt.prompt;
      args.code_file = codeFile;
    } else if (command === CommandType.EXAMPLE) {
      args.prompt_file = prompt.prompt;
      args.code_file = codeFile;
    } else if (command === CommandType.FIX) {
      args.prompt_file = prompt.prompt;
      args.code_file = codeFile;
      args.unit_test_files = testFile;
      // error_file is positional, not option
      if (options['error-file']) {
        args.error_file = options['error-file'];
        delete options['error-file'];
      }
    } else if (command === CommandType.SPLIT) {
      // Split command: pdd split INPUT_PROMPT INPUT_CODE EXAMPLE_CODE [--output-sub] [--output-modified]
      args.input_prompt = prompt.prompt;
      args.input_code = codeFile;
      if (options['example-code']) {
        args.example_code = options['example-code'];
        delete options['example-code'];
      }
    } else if (command === CommandType.CHANGE) {
      // Change command: pdd change CHANGE_PROMPT_FILE INPUT_CODE [INPUT_PROMPT_FILE] [--budget] [--output]
      if (options['change-prompt']) {
        args.change_prompt_file = options['change-prompt'];
        delete options['change-prompt'];
      }
      args.input_code = codeFile;
      args.input_prompt_file = prompt.prompt;
    } else if (command === CommandType.DETECT) {
      // Detect command: pdd detect [PROMPT_FILES...] CHANGE_FILE [--output]
      const promptFilesStr = options['prompt-files'] || '';
      const changeFile = options['change-file'] || '';
      const promptFiles = promptFilesStr.split(',').map((f: string) => f.trim()).filter(Boolean);
      args.args = [...promptFiles, changeFile].filter(Boolean);
      delete options['prompt-files'];
      delete options['change-file'];
    } else if (command === CommandType.AUTO_DEPS) {
      // Auto-deps command: pdd auto-deps PROMPT_FILE DIRECTORY_PATH [--output] [--csv] [--force-scan]
      args.prompt_file = prompt.prompt;
      if (options['directory-path']) {
        args.directory_path = options['directory-path'];
        delete options['directory-path'];
      }
    } else if (command === CommandType.CONFLICTS) {
      // Conflicts command: pdd conflicts PROMPT1 PROMPT2 [--output]
      args.prompt_file = prompt.prompt;
      if (options['prompt2']) {
        args.prompt2 = options['prompt2'];
        delete options['prompt2'];
      }
    } else if (command === CommandType.PREPROCESS) {
      // Preprocess command: pdd preprocess PROMPT_FILE [--output] [--xml] [--recursive] [--double]
      args.prompt_file = prompt.prompt;
    } else if (command === CommandType.CRASH) {
      // Crash command: pdd crash PROMPT_FILE CODE_FILE PROGRAM_FILE ERROR_FILE [options]
      args.prompt_file = prompt.prompt;
      args.code_file = codeFile;
      if (options['program-file']) {
        args.program_file = options['program-file'];
        delete options['program-file'];
      }
      if (options['error-file']) {
        args.error_file = options['error-file'];
        delete options['error-file'];
      }
    } else if (command === CommandType.VERIFY) {
      // Verify command: pdd verify PROMPT_FILE CODE_FILE VERIFICATION_PROGRAM [options]
      args.prompt_file = prompt.prompt;
      args.code_file = codeFile;
      if (options['verification-program']) {
        args.verification_program = options['verification-program'];
        delete options['verification-program'];
      }
    } else if (command === CommandType.SUBMIT_EXAMPLE) {
      // Submit Example uses fix --loop --auto-submit under the hood
      args.prompt_file = prompt.prompt;
      args.code_file = codeFile;
      args.unit_test_files = testFile;
      // Create a placeholder error file path (loop mode doesn't require existing error file)
      args.error_file = '.pdd/submit_example_errors.log';
      // Force loop and auto-submit flags
      options['loop'] = true;
      options['auto-submit'] = true;
      // Move verification-program from options to args
      if (options['verification-program']) {
        args.verification_program = options['verification-program'];
        delete options['verification-program'];
      }
    } else {
      // Default: use prompt_file
      args.prompt_file = prompt.prompt;
    }

    // Build display command
    const displayArg = command === CommandType.SYNC ? prompt.sync_basename : prompt.prompt;
    const promptName = displayArg || prompt.prompt?.split('/').pop()?.replace('.prompt', '') || 'prompt';
    let displayCommand = `pdd ${commandConfig.backendName} ${promptName}`;
    if (codeFile && command !== CommandType.SYNC) {
      displayCommand += ` ${codeFile.split('/').pop()}`;
    }

    return {
      request: {
        command: commandConfig.backendName, // Use backendName for actual CLI command
        args,
        options,
      },
      displayCommand,
    };
  };

  const handleAddToQueue = () => {
    const result = buildCommandRequest();
    if (!result || !selectedCommand || !prompt) return;

    onAddToQueue(selectedCommand, prompt, result.request, result.displayCommand);
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
                <div>
                  <label className="block text-sm font-medium text-white mb-1.5">
                    Code File
                    <span className="text-red-400 ml-1">*</span>
                  </label>
                  <div className="relative">
                    <input
                      type="text"
                      value={optionValues['_code'] || ''}
                      onChange={(e) => handleValueChange('_code', e.target.value)}
                      placeholder="e.g., src/calculator.py"
                      className={`w-full px-3 py-2.5 bg-surface-900/50 border rounded-xl text-white placeholder-surface-500 focus:outline-none focus:border-accent-500 focus:ring-1 focus:ring-accent-500/50 text-sm transition-all ${
                        prompt?.code ? 'border-green-500/50' : 'border-yellow-500/50'
                      }`}
                    />
                    {prompt?.code && (
                      <span className="absolute right-3 top-1/2 -translate-y-1/2 text-green-400 text-xs px-1.5 py-0.5 rounded bg-green-500/20">
                        detected
                      </span>
                    )}
                  </div>
                </div>
              )}

              {commandConfig.requiresTest && (
                <div>
                  <label className="block text-sm font-medium text-white mb-1.5">
                    Test File
                    <span className="text-red-400 ml-1">*</span>
                  </label>
                  <div className="relative">
                    <input
                      type="text"
                      value={optionValues['_test'] || ''}
                      onChange={(e) => handleValueChange('_test', e.target.value)}
                      placeholder="e.g., tests/test_calculator.py"
                      className={`w-full px-3 py-2.5 bg-surface-900/50 border rounded-xl text-white placeholder-surface-500 focus:outline-none focus:border-accent-500 focus:ring-1 focus:ring-accent-500/50 text-sm transition-all ${
                        prompt?.test ? 'border-green-500/50' : 'border-yellow-500/50'
                      }`}
                    />
                    {prompt?.test && (
                      <span className="absolute right-3 top-1/2 -translate-y-1/2 text-green-400 text-xs px-1.5 py-0.5 rounded bg-green-500/20">
                        detected
                      </span>
                    )}
                  </div>
                </div>
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
