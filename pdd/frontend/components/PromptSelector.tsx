import React, { useState, useEffect, useMemo, useRef, useCallback } from 'react';
import { createPortal } from 'react-dom';
import { api, PromptInfo } from '../api';
import { CommandType, CommandConfig, CommandOption } from '../types';
import { COMMANDS } from '../constants';
import CreatePromptModal from './CreatePromptModal';

interface PromptSelectorProps {
  onSelectPrompt: (prompt: PromptInfo) => void;
  onRunCommand: (command: CommandType, prompt: PromptInfo, options?: Record<string, any>) => void;
  onEditPrompt: (prompt: PromptInfo) => void;
  onCreatePrompt?: (prompt: PromptInfo) => void;
  selectedPrompt: PromptInfo | null;
  isExecuting: boolean;
}

// Options Modal Component - Modern glass design
const CommandOptionsModal: React.FC<{
  command: CommandConfig;
  prompt: PromptInfo;
  onRun: (options: Record<string, any>) => void;
  onCancel: () => void;
}> = ({ command, prompt, onRun, onCancel }) => {
  const [optionValues, setOptionValues] = useState<Record<string, any>>(() => {
    // Initialize with default values
    const defaults: Record<string, any> = {};
    command.options.forEach(opt => {
      if (opt.defaultValue !== undefined) {
        if (opt.type === 'checkbox') {
          defaults[opt.name] = opt.defaultValue === 'true' || opt.defaultValue === true;
        } else if (opt.type === 'number') {
          defaults[opt.name] = opt.defaultValue;
        } else {
          defaults[opt.name] = opt.defaultValue;
        }
      }
    });
    return defaults;
  });

  const handleValueChange = (optionName: string, value: any) => {
    setOptionValues(prev => ({ ...prev, [optionName]: value }));
  };

  const handleSubmit = (e: React.FormEvent) => {
    e.preventDefault();
    // Filter out empty/undefined values
    const cleanedOptions: Record<string, any> = {};
    Object.entries(optionValues).forEach(([key, value]) => {
      if (value !== '' && value !== undefined && value !== null) {
        cleanedOptions[key] = value;
      }
    });
    onRun(cleanedOptions);
  };

  return (
    <div className="fixed inset-0 bg-black/60 backdrop-blur-sm flex items-center justify-center z-50 p-4 animate-fade-in" onClick={onCancel}>
      <div
        className="glass rounded-2xl border border-surface-600/50 shadow-2xl w-full max-w-md animate-scale-in"
        onClick={e => e.stopPropagation()}
      >
        {/* Header */}
        <div className="px-4 sm:px-6 py-4 border-b border-surface-700/50">
          <div className="flex items-center gap-3">
            <div className="w-10 h-10 rounded-xl bg-accent-500/20 flex items-center justify-center">
              <span className="text-xl">{command.icon}</span>
            </div>
            <div>
              <h3 className="text-lg font-semibold text-white">{command.shortDescription}</h3>
              <p className="text-xs sm:text-sm text-surface-400 line-clamp-1">{command.description}</p>
            </div>
          </div>
        </div>

        {/* Form */}
        <form onSubmit={handleSubmit}>
          <div className="px-4 sm:px-6 py-4 space-y-4 max-h-[50vh] sm:max-h-[60vh] overflow-y-auto">
            {/* Target prompt info */}
            <div className="bg-surface-800/50 rounded-xl px-3 py-2.5 border border-surface-700/50">
              <div className="text-xs text-surface-400 mb-0.5">Target</div>
              <div className="text-sm text-white font-mono truncate">{prompt.sync_basename}</div>
            </div>

            {/* Command options */}
            {command.options.length > 0 ? (
              command.options.map(opt => (
                <OptionInput
                  key={opt.name}
                  option={opt}
                  value={optionValues[opt.name]}
                  onChange={(val) => handleValueChange(opt.name, val)}
                />
              ))
            ) : (
              <p className="text-surface-400 text-sm">No additional options for this command.</p>
            )}
          </div>

          {/* Footer */}
          <div className="px-4 sm:px-6 py-4 border-t border-surface-700/50 flex flex-col-reverse sm:flex-row justify-end gap-2 sm:gap-3">
            <button
              type="button"
              onClick={onCancel}
              className="w-full sm:w-auto px-4 py-2.5 rounded-xl text-sm font-medium bg-surface-700/50 text-surface-300 hover:bg-surface-600 transition-colors"
            >
              Cancel
            </button>
            <button
              type="submit"
              className="w-full sm:w-auto px-4 py-2.5 rounded-xl text-sm font-medium bg-gradient-to-r from-accent-600 to-accent-500 hover:from-accent-500 hover:to-accent-400 text-white shadow-lg shadow-accent-500/25 transition-all flex items-center justify-center gap-2"
            >
              <span>{command.icon}</span>
              <span>Run {command.shortDescription}</span>
            </button>
          </div>
        </form>
      </div>
    </div>
  );
};

// Individual option input component - Modern styling
const OptionInput: React.FC<{
  option: CommandOption;
  value: any;
  onChange: (value: any) => void;
}> = ({ option, value, onChange }) => {
  const inputId = `option-${option.name}`;

  if (option.type === 'checkbox') {
    return (
      <label htmlFor={inputId} className="flex items-start gap-3 p-3 rounded-xl bg-surface-800/30 hover:bg-surface-800/50 transition-colors cursor-pointer group">
        <input
          type="checkbox"
          id={inputId}
          checked={!!value}
          onChange={(e) => onChange(e.target.checked)}
          className="w-4 h-4 mt-0.5 rounded bg-surface-700 border-surface-600 text-accent-500 focus:ring-accent-500 focus:ring-offset-surface-800"
        />
        <div className="flex-1 min-w-0">
          <div className="text-sm font-medium text-white group-hover:text-accent-300 transition-colors">{formatOptionName(option.name)}</div>
          <div className="text-xs text-surface-400 mt-0.5">{option.description}</div>
        </div>
      </label>
    );
  }

  return (
    <div>
      <label htmlFor={inputId} className="block text-sm font-medium text-white mb-1.5">
        {formatOptionName(option.name)}
        {option.required && <span className="text-red-400 ml-1">*</span>}
      </label>
      <p className="text-xs text-surface-400 mb-2">{option.description}</p>
      {option.type === 'textarea' ? (
        <textarea
          id={inputId}
          value={value || ''}
          onChange={(e) => onChange(e.target.value)}
          placeholder={option.placeholder}
          required={option.required}
          rows={3}
          className="w-full px-3 py-2.5 bg-surface-900/50 border border-surface-600 rounded-xl text-white placeholder-surface-500 focus:outline-none focus:border-accent-500 focus:ring-1 focus:ring-accent-500/50 text-sm transition-all resize-none"
        />
      ) : (
        <input
          type={option.type === 'number' ? 'number' : 'text'}
          id={inputId}
          value={value || ''}
          onChange={(e) => onChange(option.type === 'number' ? (e.target.value ? Number(e.target.value) : '') : e.target.value)}
          placeholder={option.placeholder}
          required={option.required}
          className="w-full px-3 py-2.5 bg-surface-900/50 border border-surface-600 rounded-xl text-white placeholder-surface-500 focus:outline-none focus:border-accent-500 focus:ring-1 focus:ring-accent-500/50 text-sm transition-all"
        />
      )}
    </div>
  );
};

// Helper to format option names for display
function formatOptionName(name: string): string {
  return name
    .split('-')
    .map(word => word.charAt(0).toUpperCase() + word.slice(1))
    .join(' ');
}

const CommandButton: React.FC<{
  config: CommandConfig;
  prompt: PromptInfo;
  onClick: () => void;
  disabled: boolean;
}> = ({ config, prompt, onClick, disabled }) => {
  // Check if this command can run with the current prompt
  const canRun = () => {
    if (config.requiresCode && !prompt.code) return false;
    if (config.requiresTest && !prompt.test) return false;
    return true;
  };

  const isDisabled = disabled || !canRun();
  const missingFile = config.requiresCode && !prompt.code ? 'code' :
                     config.requiresTest && !prompt.test ? 'test' : null;

  return (
    <button
      onClick={(e) => {
        e.stopPropagation();
        onClick();
      }}
      disabled={isDisabled}
      className={`
        flex items-center gap-1.5 sm:gap-2 px-2.5 sm:px-4 py-1.5 sm:py-2 rounded-lg sm:rounded-xl text-xs sm:text-sm font-medium transition-all duration-200
        ${isDisabled
          ? 'bg-surface-700/50 text-surface-500 cursor-not-allowed'
          : 'bg-accent-600/90 hover:bg-accent-500 text-white shadow-md hover:shadow-lg hover:shadow-accent-500/20'}
      `}
      title={missingFile ? `Missing ${missingFile} file` : config.description}
    >
      <span className="text-sm">{config.icon}</span>
      <span>{config.shortDescription}</span>
    </button>
  );
};

// Dropdown button for grouped commands (e.g., Sync/Update)
// Uses Portal to render menu at body level, avoiding any parent overflow clipping
const CommandDropdown: React.FC<{
  commands: CommandConfig[];
  prompt: PromptInfo;
  onRunCommand: (command: CommandType) => void;
  disabled: boolean;
}> = ({ commands, prompt, onRunCommand, disabled }) => {
  const [isOpen, setIsOpen] = useState(false);
  const [selectedCommand, setSelectedCommand] = useState(commands[0]);
  const [menuPosition, setMenuPosition] = useState({ top: 0, left: 0, openUpward: false });
  const buttonRef = useRef<HTMLDivElement>(null);
  const menuRef = useRef<HTMLDivElement>(null);

  // Calculate menu position when opening
  const updateMenuPosition = useCallback(() => {
    if (!buttonRef.current) return;

    const rect = buttonRef.current.getBoundingClientRect();
    const menuHeight = 280; // max-h-[280px]
    const menuWidth = 220; // min-w-[220px]
    const padding = 8;

    // Check if there's enough space below
    const spaceBelow = window.innerHeight - rect.bottom;
    const spaceAbove = rect.top;
    const openUpward = spaceBelow < menuHeight + padding && spaceAbove > spaceBelow;

    // Calculate left position, keeping menu within viewport
    let left = rect.left;
    if (left + menuWidth > window.innerWidth - padding) {
      left = window.innerWidth - menuWidth - padding;
    }
    if (left < padding) {
      left = padding;
    }

    setMenuPosition({
      top: openUpward ? rect.top - padding : rect.bottom + padding,
      left,
      openUpward,
    });
  }, []);

  // Close dropdown when clicking outside
  useEffect(() => {
    if (!isOpen) return;

    const handleClickOutside = (event: MouseEvent) => {
      const target = event.target as Node;
      if (
        buttonRef.current && !buttonRef.current.contains(target) &&
        menuRef.current && !menuRef.current.contains(target)
      ) {
        setIsOpen(false);
      }
    };

    const handleScroll = () => {
      updateMenuPosition();
    };

    const handleResize = () => {
      setIsOpen(false);
    };

    document.addEventListener('mousedown', handleClickOutside);
    window.addEventListener('scroll', handleScroll, true);
    window.addEventListener('resize', handleResize);

    return () => {
      document.removeEventListener('mousedown', handleClickOutside);
      window.removeEventListener('scroll', handleScroll, true);
      window.removeEventListener('resize', handleResize);
    };
  }, [isOpen, updateMenuPosition]);

  // Update position when opening
  useEffect(() => {
    if (isOpen) {
      updateMenuPosition();
    }
  }, [isOpen, updateMenuPosition]);

  const canRun = (config: CommandConfig) => {
    if (config.requiresCode && !prompt.code) return false;
    if (config.requiresTest && !prompt.test) return false;
    return true;
  };

  const isMainDisabled = disabled || !canRun(selectedCommand);

  const handleToggle = (e: React.MouseEvent) => {
    e.stopPropagation();
    setIsOpen(!isOpen);
  };

  // Dropdown menu content
  const menuContent = isOpen ? (
    <div
      ref={menuRef}
      className="fixed bg-surface-800 rounded-xl border border-surface-600 shadow-2xl min-w-[220px] max-h-[280px] overflow-y-auto animate-fade-in"
      style={{
        top: menuPosition.openUpward ? 'auto' : menuPosition.top,
        bottom: menuPosition.openUpward ? window.innerHeight - menuPosition.top : 'auto',
        left: menuPosition.left,
        zIndex: 9999,
        boxShadow: '0 10px 50px rgba(0, 0, 0, 0.6)',
      }}
      onClick={(e) => e.stopPropagation()}
    >
      {commands.map((cmd, idx) => {
        const cmdDisabled = !canRun(cmd);
        return (
          <button
            key={cmd.name}
            onClick={(e) => {
              e.stopPropagation();
              setSelectedCommand(cmd);
              setIsOpen(false);
              if (!cmdDisabled) {
                onRunCommand(cmd.name);
              }
            }}
            disabled={cmdDisabled}
            className={`
              w-full flex items-center gap-2.5 px-4 py-3 text-sm text-left transition-colors
              ${cmdDisabled
                ? 'text-surface-500 cursor-not-allowed'
                : 'text-white hover:bg-surface-700'}
              ${selectedCommand.name === cmd.name ? 'bg-accent-600/20' : ''}
              ${idx !== commands.length - 1 ? 'border-b border-surface-700' : ''}
            `}
          >
            <span className="text-base">{cmd.icon}</span>
            <div className="flex-1 min-w-0">
              <div className="font-medium text-sm">{cmd.shortDescription}</div>
              <div className="text-xs text-surface-400">{cmd.description.slice(0, 50)}...</div>
            </div>
            {selectedCommand.name === cmd.name && (
              <svg className="w-4 h-4 text-accent-400 flex-shrink-0" fill="none" stroke="currentColor" viewBox="0 0 24 24">
                <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M5 13l4 4L19 7" />
              </svg>
            )}
          </button>
        );
      })}
    </div>
  ) : null;

  return (
    <div className="relative inline-flex" ref={buttonRef} onClick={(e) => e.stopPropagation()}>
      {/* Main button */}
      <button
        onClick={(e) => {
          e.stopPropagation();
          if (!isMainDisabled) onRunCommand(selectedCommand.name);
        }}
        disabled={isMainDisabled}
        className={`
          flex items-center gap-1.5 sm:gap-2 px-2.5 sm:px-4 py-1.5 sm:py-2 rounded-l-lg sm:rounded-l-xl text-xs sm:text-sm font-medium transition-all duration-200
          ${isMainDisabled
            ? 'bg-surface-700/50 text-surface-500 cursor-not-allowed'
            : 'bg-accent-600/90 hover:bg-accent-500 text-white shadow-md'}
        `}
        title={selectedCommand.description}
      >
        <span className="text-sm">{selectedCommand.icon}</span>
        <span>{selectedCommand.shortDescription}</span>
      </button>

      {/* Dropdown toggle */}
      <button
        onClick={handleToggle}
        disabled={disabled}
        className={`
          px-1.5 sm:px-2 py-1.5 sm:py-2 rounded-r-lg sm:rounded-r-xl text-sm font-medium transition-all duration-200 border-l border-accent-700/50
          ${disabled
            ? 'bg-surface-700/50 text-surface-500 cursor-not-allowed'
            : 'bg-accent-600/90 hover:bg-accent-500 text-white'}
        `}
      >
        <svg className={`w-3.5 h-3.5 sm:w-4 sm:h-4 transition-transform duration-200 ${isOpen ? 'rotate-180' : ''}`} fill="none" stroke="currentColor" viewBox="0 0 24 24">
          <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M19 9l-7 7-7-7" />
        </svg>
      </button>

      {/* Portal-based dropdown menu - renders at document body level */}
      {menuContent && createPortal(menuContent, document.body)}
    </div>
  );
};

// Language badge colors - Modern gradient approach
const LANGUAGE_COLORS: Record<string, string> = {
  python: 'bg-blue-500/15 text-blue-300 border-blue-500/30',
  typescript: 'bg-cyan-500/15 text-cyan-300 border-cyan-500/30',
  javascript: 'bg-yellow-500/15 text-yellow-300 border-yellow-500/30',
  java: 'bg-orange-500/15 text-orange-300 border-orange-500/30',
  go: 'bg-teal-500/15 text-teal-300 border-teal-500/30',
  rust: 'bg-red-500/15 text-red-300 border-red-500/30',
};

const PromptCard: React.FC<{
  prompt: PromptInfo;
  isSelected: boolean;
  onSelect: () => void;
  onRunCommand: (command: CommandType, options?: Record<string, any>) => void;
  onEditPrompt: () => void;
  isExecuting: boolean;
}> = ({ prompt, isSelected, onSelect, onRunCommand, onEditPrompt, isExecuting }) => {
  const [modalCommand, setModalCommand] = useState<CommandConfig | null>(null);

  const languageColor = prompt.language
    ? LANGUAGE_COLORS[prompt.language] || 'bg-surface-700/50 text-surface-300 border-surface-600'
    : 'bg-surface-700/50 text-surface-300 border-surface-600';

  const handleCommandClick = (command: CommandType) => {
    const config = COMMANDS[command];
    // Show modal for commands with options, otherwise run directly
    if (config.options && config.options.length > 0) {
      setModalCommand(config);
    } else {
      onRunCommand(command);
    }
  };

  const handleRunWithOptions = (options: Record<string, any>) => {
    if (modalCommand) {
      onRunCommand(modalCommand.name, options);
      setModalCommand(null);
    }
  };

  const handleCardClick = (e: React.MouseEvent) => {
    e.stopPropagation();
    onSelect();
  };

  const handleEditClick = (e: React.MouseEvent) => {
    e.stopPropagation();
    onEditPrompt();
  };

  return (
    <>
      <div
        className={`
          glass rounded-xl sm:rounded-2xl border transition-all duration-200 card-hover
          ${isSelected
            ? 'border-accent-500/50 shadow-lg shadow-accent-500/10 ring-1 ring-accent-500/20'
            : 'border-surface-700/50 hover:border-surface-600'}
        `}
      >
        {/* Card header - clickable to select */}
        <div className="p-3 sm:p-4 cursor-pointer" onClick={handleCardClick}>
          <div className="flex items-start justify-between gap-2 mb-2 sm:mb-3">
            <div className="flex items-center gap-2 flex-wrap min-w-0">
              <h3 className="text-base sm:text-lg font-semibold text-white truncate">{prompt.sync_basename}</h3>
              {prompt.language && (
                <span className={`px-2 py-0.5 rounded-full text-[10px] sm:text-xs border font-medium ${languageColor}`}>
                  {prompt.language}
                </span>
              )}
            </div>
            <div className="flex items-center gap-2 flex-shrink-0">
              {/* Edit button to open full-screen PromptSpace */}
              <button
                onClick={handleEditClick}
                className="px-2 sm:px-3 py-1 sm:py-1.5 rounded-lg text-xs sm:text-sm font-medium flex items-center gap-1 sm:gap-1.5 transition-all duration-200 bg-surface-700/50 text-surface-300 hover:bg-accent-600 hover:text-white border border-surface-600/50 hover:border-accent-500/50"
                title="Open in Prompt Space"
              >
                <svg className="w-3.5 h-3.5 sm:w-4 sm:h-4" fill="none" stroke="currentColor" viewBox="0 0 24 24">
                  <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M11 5H6a2 2 0 00-2 2v11a2 2 0 002 2h11a2 2 0 002-2v-5m-1.414-9.414a2 2 0 112.828 2.828L11.828 15H9v-2.828l8.586-8.586z" />
                </svg>
                <span className="hidden sm:inline">Open</span>
              </button>
              {isSelected && (
                <span className="px-2 py-1 rounded-full bg-accent-500/20 text-accent-300 text-[10px] sm:text-xs font-medium border border-accent-500/30">
                  Selected
                </span>
              )}
            </div>
          </div>
          <p className="text-[10px] sm:text-xs text-surface-400 font-mono mb-2 sm:mb-3 truncate">{prompt.prompt}</p>

          {/* Related files - responsive grid */}
          <div className="flex gap-1.5 sm:gap-2 flex-wrap">
            <FileTag label="Prompt" path={prompt.prompt} exists={true} color="purple" />
            <FileTag label="Code" path={prompt.code} exists={!!prompt.code} color="green" />
            <FileTag label="Test" path={prompt.test} exists={!!prompt.test} color="yellow" />
            <FileTag label="Example" path={prompt.example} exists={!!prompt.example} color="blue" />
          </div>
        </div>

        {/* Command buttons - only show when selected */}
        {isSelected && (
          <div className="flex gap-1.5 sm:gap-2 flex-wrap px-3 sm:px-4 pb-3 sm:pb-4 pt-2 sm:pt-3 border-t border-surface-700/50 bg-surface-800/30 animate-fade-in overflow-visible relative">
            {(() => {
              const commands = Object.values(COMMANDS).filter(cmd => cmd.requiresPrompt);
              const groups: Record<string, CommandConfig[]> = {};
              const ungrouped: CommandConfig[] = [];

              // Separate grouped and ungrouped commands
              commands.forEach(cmd => {
                if (cmd.group) {
                  if (!groups[cmd.group]) groups[cmd.group] = [];
                  groups[cmd.group].push(cmd);
                } else {
                  ungrouped.push(cmd);
                }
              });

              return (
                <>
                  {/* Render grouped commands as dropdowns */}
                  {Object.entries(groups).map(([groupName, groupCommands]) => (
                    <CommandDropdown
                      key={groupName}
                      commands={groupCommands}
                      prompt={prompt}
                      onRunCommand={handleCommandClick}
                      disabled={isExecuting}
                    />
                  ))}

                  {/* Render ungrouped commands as regular buttons */}
                  {ungrouped.map(cmd => (
                    <CommandButton
                      key={cmd.name}
                      config={cmd}
                      prompt={prompt}
                      onClick={() => handleCommandClick(cmd.name)}
                      disabled={isExecuting}
                    />
                  ))}
                </>
              );
            })()}
          </div>
        )}
      </div>

      {/* Options Modal */}
      {modalCommand && (
        <CommandOptionsModal
          command={modalCommand}
          prompt={prompt}
          onRun={handleRunWithOptions}
          onCancel={() => setModalCommand(null)}
        />
      )}
    </>
  );
};

const FileTag: React.FC<{
  label: string;
  path?: string;
  exists: boolean;
  color: 'purple' | 'green' | 'yellow' | 'blue';
}> = ({ label, path, exists, color }) => {
  const colorClasses = {
    purple: exists ? 'bg-purple-500/15 text-purple-300 border-purple-500/30' : 'bg-surface-800/50 text-surface-500 border-surface-700/50',
    green: exists ? 'bg-green-500/15 text-green-300 border-green-500/30' : 'bg-surface-800/50 text-surface-500 border-surface-700/50',
    yellow: exists ? 'bg-yellow-500/15 text-yellow-300 border-yellow-500/30' : 'bg-surface-800/50 text-surface-500 border-surface-700/50',
    blue: exists ? 'bg-blue-500/15 text-blue-300 border-blue-500/30' : 'bg-surface-800/50 text-surface-500 border-surface-700/50',
  };

  return (
    <span
      className={`inline-flex items-center gap-1 px-1.5 sm:px-2 py-0.5 rounded-md text-[10px] sm:text-xs border font-medium ${colorClasses[color]}`}
      title={path || `No ${label.toLowerCase()} file`}
    >
      <span className={exists ? 'text-green-400' : 'text-surface-500'}>{exists ? '✓' : '✗'}</span>
      <span>{label}</span>
    </span>
  );
};

const PromptSelector: React.FC<PromptSelectorProps> = ({
  onSelectPrompt,
  onRunCommand,
  onEditPrompt,
  onCreatePrompt,
  selectedPrompt,
  isExecuting,
}) => {
  const [prompts, setPrompts] = useState<PromptInfo[]>([]);
  const [loading, setLoading] = useState(true);
  const [error, setError] = useState<string | null>(null);
  const [searchQuery, setSearchQuery] = useState('');
  const [showCreateModal, setShowCreateModal] = useState(false);
  const [isCreating, setIsCreating] = useState(false);

  // Filter prompts based on search query
  const filteredPrompts = useMemo(() => {
    if (!searchQuery.trim()) return prompts;
    const query = searchQuery.toLowerCase();
    return prompts.filter(p =>
      p.sync_basename.toLowerCase().includes(query) ||
      p.prompt.toLowerCase().includes(query) ||
      (p.language && p.language.toLowerCase().includes(query))
    );
  }, [prompts, searchQuery]);

  useEffect(() => {
    loadPrompts();
  }, []);

  const loadPrompts = async () => {
    setLoading(true);
    setError(null);
    try {
      const data = await api.listPrompts();
      setPrompts(data);
    } catch (e: any) {
      setError(e.message || 'Failed to load prompts');
    } finally {
      setLoading(false);
    }
  };

  // Handle creating a new prompt
  const handleCreatePrompt = async (promptData: { path: string; content: string; info: PromptInfo }) => {
    setIsCreating(true);
    try {
      await api.writeFile(promptData.path, promptData.content);
      await loadPrompts();
      setShowCreateModal(false);
      // Navigate to PromptSpace to edit the new prompt
      if (onCreatePrompt) {
        onCreatePrompt(promptData.info);
      }
    } catch (e: any) {
      throw new Error(e.message || 'Failed to create prompt');
    } finally {
      setIsCreating(false);
    }
  };

  if (loading) {
    return (
      <div className="flex flex-col items-center justify-center py-16 sm:py-20">
        <div className="w-10 h-10 rounded-xl bg-accent-500/20 flex items-center justify-center mb-4">
          <svg className="animate-spin h-5 w-5 text-accent-400" viewBox="0 0 24 24">
            <circle className="opacity-25" cx="12" cy="12" r="10" stroke="currentColor" strokeWidth="4" fill="none" />
            <path className="opacity-75" fill="currentColor" d="M4 12a8 8 0 018-8V0C5.373 0 0 5.373 0 12h4z" />
          </svg>
        </div>
        <div className="text-surface-400 text-sm">Loading prompts...</div>
      </div>
    );
  }

  if (error) {
    return (
      <div className="flex flex-col items-center justify-center py-16 sm:py-20">
        <div className="w-12 h-12 rounded-xl bg-red-500/20 flex items-center justify-center mb-4">
          <svg className="w-6 h-6 text-red-400" fill="none" stroke="currentColor" viewBox="0 0 24 24">
            <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M12 9v2m0 4h.01m-6.938 4h13.856c1.54 0 2.502-1.667 1.732-3L13.732 4c-.77-1.333-2.694-1.333-3.464 0L3.34 16c-.77 1.333.192 3 1.732 3z" />
          </svg>
        </div>
        <div className="text-red-400 mb-2 text-center">{error}</div>
        <button
          onClick={loadPrompts}
          className="px-4 py-2 bg-surface-700/50 hover:bg-surface-600 rounded-xl text-sm text-white transition-colors border border-surface-600"
        >
          Try Again
        </button>
      </div>
    );
  }

  if (prompts.length === 0) {
    return (
      <div className="flex flex-col items-center justify-center py-16 sm:py-20">
        <div className="w-14 h-14 rounded-2xl bg-surface-700/50 flex items-center justify-center mb-5">
          <svg className="w-7 h-7 text-surface-400" fill="none" stroke="currentColor" viewBox="0 0 24 24">
            <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M9 12h6m-6 4h6m2 5H7a2 2 0 01-2-2V5a2 2 0 012-2h5.586a1 1 0 01.707.293l5.414 5.414a1 1 0 01.293.707V19a2 2 0 01-2 2z" />
          </svg>
        </div>
        <div className="text-surface-200 mb-2 font-semibold text-lg">No prompts found</div>
        <p className="text-surface-500 text-sm text-center mb-6 max-w-sm">
          Get started by creating your first prompt, or add <code className="bg-surface-800/80 px-1.5 py-0.5 rounded text-accent-300">.prompt</code> files to the <code className="bg-surface-800/80 px-1.5 py-0.5 rounded text-accent-300">prompts/</code> directory.
        </p>
        <button
          onClick={() => setShowCreateModal(true)}
          className="flex items-center gap-2 px-5 py-2.5 bg-gradient-to-r from-accent-600 to-accent-500 hover:from-accent-500 hover:to-accent-400 text-white rounded-xl font-medium shadow-lg shadow-accent-500/25 transition-all"
        >
          <svg className="w-4 h-4" fill="none" stroke="currentColor" viewBox="0 0 24 24">
            <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M12 4v16m8-8H4" />
          </svg>
          Create Your First Prompt
        </button>

        {showCreateModal && (
          <CreatePromptModal
            onClose={() => setShowCreateModal(false)}
            onCreate={handleCreatePrompt}
            isCreating={isCreating}
            existingPrompts={prompts}
          />
        )}
      </div>
    );
  }

  return (
    <div className="space-y-3 sm:space-y-4">
      {/* Header with title and refresh */}
      <div className="flex items-center justify-between">
        <h2 className="text-base sm:text-lg font-semibold text-white flex items-center gap-2">
          <span className="hidden sm:inline">Your Prompts</span>
          <span className="sm:hidden">Prompts</span>
          <span className="px-2 py-0.5 rounded-full bg-accent-500/20 text-accent-300 text-xs font-medium">
            {filteredPrompts.length}{searchQuery ? `/${prompts.length}` : ''}
          </span>
        </h2>
        <div className="flex items-center gap-2">
          <button
            onClick={() => setShowCreateModal(true)}
            className="flex items-center gap-1.5 px-2.5 sm:px-3 py-1.5 text-xs sm:text-sm bg-accent-600 hover:bg-accent-500 text-white rounded-lg transition-colors"
            title="Create new prompt"
          >
            <svg className="w-3.5 h-3.5" fill="none" stroke="currentColor" viewBox="0 0 24 24">
              <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M12 4v16m8-8H4" />
            </svg>
            <span className="hidden sm:inline">New</span>
          </button>
          <button
            onClick={loadPrompts}
            className="flex items-center gap-1.5 px-2.5 sm:px-3 py-1.5 text-xs sm:text-sm text-surface-400 hover:text-white bg-surface-800/50 hover:bg-surface-700 rounded-lg transition-colors border border-surface-700/50"
            title="Refresh"
          >
            <svg className="w-3.5 h-3.5" fill="none" stroke="currentColor" viewBox="0 0 24 24">
              <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M4 4v5h.582m15.356 2A8.001 8.001 0 004.582 9m0 0H9m11 11v-5h-.581m0 0a8.003 8.003 0 01-15.357-2m15.357 2H15" />
            </svg>
            <span className="hidden sm:inline">Refresh</span>
          </button>
        </div>
      </div>

      {/* Search input - Modern design */}
      <div className="relative">
        <input
          type="text"
          placeholder="Search prompts..."
          value={searchQuery}
          onChange={(e) => setSearchQuery(e.target.value)}
          className="w-full px-3 sm:px-4 py-2.5 sm:py-3 pl-9 sm:pl-11 bg-surface-800/50 border border-surface-600/50 rounded-xl text-white placeholder-surface-500 focus:outline-none focus:border-accent-500 focus:ring-1 focus:ring-accent-500/50 text-sm sm:text-base transition-all"
        />
        <span className="absolute left-3 sm:left-4 top-1/2 -translate-y-1/2 text-surface-400">
          <svg className="w-4 h-4" fill="none" stroke="currentColor" viewBox="0 0 24 24">
            <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M21 21l-6-6m2-5a7 7 0 11-14 0 7 7 0 0114 0z" />
          </svg>
        </span>
        {searchQuery && (
          <button
            onClick={() => setSearchQuery('')}
            className="absolute right-3 top-1/2 -translate-y-1/2 text-surface-400 hover:text-white p-1 rounded-lg hover:bg-surface-700/50 transition-colors"
          >
            <svg className="w-4 h-4" fill="none" stroke="currentColor" viewBox="0 0 24 24">
              <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M6 18L18 6M6 6l12 12" />
            </svg>
          </button>
        )}
      </div>

      {filteredPrompts.length === 0 ? (
        <div className="flex flex-col items-center justify-center py-12 sm:py-16">
          <div className="w-10 h-10 rounded-xl bg-surface-700/50 flex items-center justify-center mb-3">
            <svg className="w-5 h-5 text-surface-400" fill="none" stroke="currentColor" viewBox="0 0 24 24">
              <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M21 21l-6-6m2-5a7 7 0 11-14 0 7 7 0 0114 0z" />
            </svg>
          </div>
          <div className="text-surface-400 text-sm text-center">
            No prompts matching "<span className="text-white">{searchQuery}</span>"
          </div>
        </div>
      ) : (
        <div className="grid gap-3 sm:gap-4">
          {filteredPrompts.map(prompt => (
            <PromptCard
              key={prompt.prompt}
              prompt={prompt}
              isSelected={selectedPrompt?.prompt === prompt.prompt}
              onSelect={() => onSelectPrompt(prompt)}
              onRunCommand={(cmd, options) => onRunCommand(cmd, prompt, options)}
              onEditPrompt={() => onEditPrompt(prompt)}
              isExecuting={isExecuting}
            />
          ))}
        </div>
      )}

      {/* Create Prompt Modal */}
      {showCreateModal && (
        <CreatePromptModal
          onClose={() => setShowCreateModal(false)}
          onCreate={handleCreatePrompt}
          isCreating={isCreating}
          existingPrompts={prompts}
        />
      )}
    </div>
  );
};

export default PromptSelector;
