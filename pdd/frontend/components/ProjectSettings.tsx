import React, { useState, useEffect, useCallback } from 'react';
import { api, AuthStatus } from '../api';
import { PddrcConfig, PddrcContext, PddrcContextDefaults } from '../types';
import { Cog6ToothIcon, ChevronDownIcon, ChevronUpIcon, TrashIcon, PlusIcon, FolderIcon, SpinnerIcon } from './Icon';
import Tooltip from './Tooltip';
import FilePickerInput from './FilePickerInput';

// Available languages for dropdown
const LANGUAGES = [
  'python',
  'typescript',
  'javascript',
  'java',
  'go',
  'rust',
  'cpp',
  'c',
  'csharp',
  'ruby',
  'swift',
  'kotlin',
];

// Default config when no .pddrc exists
const DEFAULT_CONFIG: PddrcConfig = {
  contexts: {
    default: {
      paths: ['**'],
      defaults: {
        generate_output_path: 'src/',
        test_output_path: 'tests/',
        example_output_path: 'examples/',
        default_language: 'python',
      },
    },
  },
};

// Field labels for user-friendly display
const FIELD_LABELS: Record<keyof PddrcContextDefaults, { label: string; description: string; placeholder: string }> = {
  generate_output_path: {
    label: 'Code Output Directory',
    description: 'Where generated code files will be saved',
    placeholder: 'src/',
  },
  test_output_path: {
    label: 'Test Output Directory',
    description: 'Where generated test files will be saved',
    placeholder: 'tests/',
  },
  example_output_path: {
    label: 'Example Output Directory',
    description: 'Where generated example files will be saved',
    placeholder: 'examples/',
  },
  prompts_dir: {
    label: 'Prompts Directory',
    description: 'Custom directory for prompt files',
    placeholder: 'prompts/',
  },
  default_language: {
    label: 'Default Language',
    description: 'Default programming language for this context',
    placeholder: 'python',
  },
  strength: {
    label: 'Model Strength',
    description: 'AI model strength (0.0 to 1.0)',
    placeholder: '0.75',
  },
  temperature: {
    label: 'Temperature',
    description: 'AI model temperature (0.0 to 2.0)',
    placeholder: '0.0',
  },
  budget: {
    label: 'Budget',
    description: 'Maximum cost budget for operations',
    placeholder: '5.0',
  },
  max_attempts: {
    label: 'Max Attempts',
    description: 'Maximum retry attempts for operations',
    placeholder: '3',
  },
};

interface ContextCardProps {
  name: string;
  context: PddrcContext;
  isDefault: boolean;
  onChange: (name: string, context: PddrcContext) => void;
  onDelete: (name: string) => void;
  onRename: (oldName: string, newName: string) => void;
}

const ContextCard: React.FC<ContextCardProps> = ({
  name,
  context,
  isDefault,
  onChange,
  onDelete,
  onRename,
}) => {
  const [isExpanded, setIsExpanded] = useState(true);
  const [showAdvanced, setShowAdvanced] = useState(false);
  const [editingName, setEditingName] = useState(false);
  const [newName, setNewName] = useState(name);

  const handleDefaultsChange = (key: keyof PddrcContextDefaults, value: string | number | undefined) => {
    const newDefaults = { ...context.defaults };
    if (value === '' || value === undefined) {
      delete newDefaults[key];
    } else {
      (newDefaults as any)[key] = value;
    }
    onChange(name, { ...context, defaults: newDefaults });
  };

  const handlePathsChange = (value: string) => {
    const paths = value.split(',').map(p => p.trim()).filter(Boolean);
    onChange(name, { ...context, paths });
  };

  // Ensure paths and defaults are always valid
  const paths = context.paths || [];
  const defaults = context.defaults || {};

  const handleNameSubmit = () => {
    if (newName && newName !== name) {
      onRename(name, newName);
    }
    setEditingName(false);
  };

  return (
    <div className="glass rounded-xl border border-surface-700/50 overflow-hidden">
      {/* Header */}
      <div
        className="flex items-center justify-between p-4 cursor-pointer hover:bg-surface-800/50 transition-colors"
        onClick={() => setIsExpanded(!isExpanded)}
      >
        <div className="flex items-center gap-3">
          <FolderIcon className="w-5 h-5 text-accent-400" />
          {editingName && !isDefault ? (
            <input
              type="text"
              value={newName}
              onChange={e => setNewName(e.target.value)}
              onBlur={handleNameSubmit}
              onKeyDown={e => {
                if (e.key === 'Enter') handleNameSubmit();
                if (e.key === 'Escape') {
                  setNewName(name);
                  setEditingName(false);
                }
              }}
              onClick={e => e.stopPropagation()}
              className="px-2 py-1 bg-surface-900 border border-surface-600 rounded text-white text-sm focus:outline-none focus:border-accent-500"
              autoFocus
            />
          ) : (
            <span
              className="font-medium text-white"
              onDoubleClick={e => {
                if (!isDefault) {
                  e.stopPropagation();
                  setEditingName(true);
                }
              }}
            >
              {name}
              {isDefault && <span className="ml-2 text-xs text-surface-400">(default)</span>}
            </span>
          )}
        </div>
        <div className="flex items-center gap-2">
          {!isDefault && (
            <Tooltip content="Delete context">
              <button
                onClick={e => {
                  e.stopPropagation();
                  onDelete(name);
                }}
                className="p-1.5 hover:bg-red-500/20 rounded-lg transition-colors text-surface-400 hover:text-red-400"
              >
                <TrashIcon className="w-4 h-4" />
              </button>
            </Tooltip>
          )}
          {isExpanded ? (
            <ChevronUpIcon className="w-5 h-5 text-surface-400" />
          ) : (
            <ChevronDownIcon className="w-5 h-5 text-surface-400" />
          )}
        </div>
      </div>

      {/* Content */}
      {isExpanded && (
        <div className="p-4 pt-0 space-y-4">
          {/* Path patterns */}
          <div>
            <label className="block text-sm font-medium text-surface-300 mb-1">
              File Patterns
            </label>
            <input
              type="text"
              value={paths.join(', ')}
              onChange={e => handlePathsChange(e.target.value)}
              placeholder="**, frontend/**, backend/**"
              className="w-full px-3 py-2 bg-surface-900/50 border border-surface-600 rounded-lg text-white placeholder-surface-500 focus:outline-none focus:border-accent-500 text-sm"
            />
            <p className="mt-1 text-xs text-surface-500">
              Glob patterns to match files (e.g., frontend/**, **/*.py)
            </p>
          </div>

          {/* Output paths */}
          <div className="grid grid-cols-1 sm:grid-cols-2 gap-4">
            <FilePickerInput
              label={FIELD_LABELS.generate_output_path.label}
              value={defaults.generate_output_path || ''}
              onChange={(path) => handleDefaultsChange('generate_output_path', path)}
              placeholder={FIELD_LABELS.generate_output_path.placeholder}
              description={FIELD_LABELS.generate_output_path.description}
              directoryMode
              title="Select Code Output Directory"
            />
            <FilePickerInput
              label={FIELD_LABELS.test_output_path.label}
              value={defaults.test_output_path || ''}
              onChange={(path) => handleDefaultsChange('test_output_path', path)}
              placeholder={FIELD_LABELS.test_output_path.placeholder}
              description={FIELD_LABELS.test_output_path.description}
              directoryMode
              title="Select Test Output Directory"
            />
            <FilePickerInput
              label={FIELD_LABELS.example_output_path.label}
              value={defaults.example_output_path || ''}
              onChange={(path) => handleDefaultsChange('example_output_path', path)}
              placeholder={FIELD_LABELS.example_output_path.placeholder}
              description={FIELD_LABELS.example_output_path.description}
              directoryMode
              title="Select Example Output Directory"
            />
            <div>
              <label className="block text-sm font-medium text-surface-300 mb-1">
                {FIELD_LABELS.default_language.label}
              </label>
              <select
                value={defaults.default_language || ''}
                onChange={e => handleDefaultsChange('default_language', e.target.value)}
                className="w-full px-3 py-2 bg-surface-900/50 border border-surface-600 rounded-lg text-white focus:outline-none focus:border-accent-500 text-sm"
              >
                <option value="">Select language...</option>
                {LANGUAGES.map(lang => (
                  <option key={lang} value={lang}>
                    {lang.charAt(0).toUpperCase() + lang.slice(1)}
                  </option>
                ))}
              </select>
            </div>
          </div>

          {/* Advanced options toggle */}
          <button
            onClick={() => setShowAdvanced(!showAdvanced)}
            className="flex items-center gap-2 text-sm text-surface-400 hover:text-white transition-colors"
          >
            {showAdvanced ? (
              <ChevronUpIcon className="w-4 h-4" />
            ) : (
              <ChevronDownIcon className="w-4 h-4" />
            )}
            Advanced Options
          </button>

          {/* Advanced options */}
          {showAdvanced && (
            <div className="grid grid-cols-1 sm:grid-cols-2 gap-4 p-3 bg-surface-800/30 rounded-lg">
              <FilePickerInput
                label={FIELD_LABELS.prompts_dir.label}
                value={defaults.prompts_dir || ''}
                onChange={(path) => handleDefaultsChange('prompts_dir', path)}
                placeholder={FIELD_LABELS.prompts_dir.placeholder}
                description={FIELD_LABELS.prompts_dir.description}
                directoryMode
                title="Select Prompts Directory"
              />
              <div>
                <label className="block text-sm font-medium text-surface-300 mb-1">
                  {FIELD_LABELS.strength.label}
                </label>
                <input
                  type="number"
                  min="0"
                  max="1"
                  step="0.05"
                  value={defaults.strength ?? ''}
                  onChange={e => handleDefaultsChange('strength', e.target.value ? parseFloat(e.target.value) : undefined)}
                  placeholder={FIELD_LABELS.strength.placeholder}
                  className="w-full px-3 py-2 bg-surface-900/50 border border-surface-600 rounded-lg text-white placeholder-surface-500 focus:outline-none focus:border-accent-500 text-sm"
                />
              </div>
              <div>
                <label className="block text-sm font-medium text-surface-300 mb-1">
                  {FIELD_LABELS.temperature.label}
                </label>
                <input
                  type="number"
                  min="0"
                  max="2"
                  step="0.1"
                  value={defaults.temperature ?? ''}
                  onChange={e => handleDefaultsChange('temperature', e.target.value ? parseFloat(e.target.value) : undefined)}
                  placeholder={FIELD_LABELS.temperature.placeholder}
                  className="w-full px-3 py-2 bg-surface-900/50 border border-surface-600 rounded-lg text-white placeholder-surface-500 focus:outline-none focus:border-accent-500 text-sm"
                />
              </div>
              <div>
                <label className="block text-sm font-medium text-surface-300 mb-1">
                  {FIELD_LABELS.budget.label}
                </label>
                <input
                  type="number"
                  min="0"
                  step="1"
                  value={defaults.budget ?? ''}
                  onChange={e => handleDefaultsChange('budget', e.target.value ? parseFloat(e.target.value) : undefined)}
                  placeholder={FIELD_LABELS.budget.placeholder}
                  className="w-full px-3 py-2 bg-surface-900/50 border border-surface-600 rounded-lg text-white placeholder-surface-500 focus:outline-none focus:border-accent-500 text-sm"
                />
              </div>
            </div>
          )}
        </div>
      )}
    </div>
  );
};

const ProjectSettings: React.FC = () => {
  const [config, setConfig] = useState<PddrcConfig | null>(null);
  const [originalConfig, setOriginalConfig] = useState<string>('');
  const [loading, setLoading] = useState(true);
  const [saving, setSaving] = useState(false);
  const [error, setError] = useState<string | null>(null);
  const [saveSuccess, setSaveSuccess] = useState(false);

  // Auth state
  const [authStatus, setAuthStatus] = useState<AuthStatus | null>(null);
  const [authLoading, setAuthLoading] = useState(false);
  const [authResult, setAuthResult] = useState<{ success: boolean; message: string } | null>(null);

  const loadConfig = async () => {
    setLoading(true);
    setError(null);
    try {
      console.log('[ProjectSettings] Loading .pddrc configuration...');
      const loadedConfig = await api.getPddrc();
      console.log('[ProjectSettings] Loaded config:', loadedConfig);
      if (loadedConfig) {
        setConfig(loadedConfig);
        setOriginalConfig(JSON.stringify(loadedConfig));
      } else {
        // No .pddrc exists, use default
        console.log('[ProjectSettings] No .pddrc found, using defaults');
        setConfig(DEFAULT_CONFIG);
        setOriginalConfig('');
      }
    } catch (e) {
      console.error('[ProjectSettings] Error loading config:', e);
      setError(e instanceof Error ? e.message : 'Failed to load configuration');
      setConfig(DEFAULT_CONFIG);
    } finally {
      console.log('[ProjectSettings] Loading complete');
      setLoading(false);
    }
  };

  // Load config on mount
  useEffect(() => {
    loadConfig();
  }, []);

  // Load auth status on mount
  useEffect(() => {
    const loadAuthStatus = async () => {
      try {
        const status = await api.getAuthStatus();
        setAuthStatus(status);
      } catch (e) {
        setAuthStatus({ authenticated: false, cached: false, expires_at: null });
      }
    };
    loadAuthStatus();
  }, []);

  const handleLogout = async () => {
    setAuthLoading(true);
    setAuthResult(null);
    try {
      const result = await api.logout();
      if (result.success) {
        setAuthResult({
          success: true,
          message: 'Tokens cleared. Run any pdd command to re-authenticate with GitHub.',
        });
        // Refresh auth status
        const newStatus = await api.getAuthStatus();
        setAuthStatus(newStatus);
      } else {
        setAuthResult(result);
      }
    } catch (e) {
      setAuthResult({
        success: false,
        message: e instanceof Error ? e.message : 'Failed to clear tokens',
      });
    } finally {
      setAuthLoading(false);
    }
  };

  const hasChanges = useCallback(() => {
    if (!config) return false;
    const currentConfig = JSON.stringify(config);
    return currentConfig !== originalConfig;
  }, [config, originalConfig]);

  const handleSave = async () => {
    if (!config) return;
    setSaving(true);
    setError(null);
    try {
      const result = await api.savePddrc(config);
      if (result.success) {
        setOriginalConfig(JSON.stringify(config));
        setSaveSuccess(true);
        setTimeout(() => setSaveSuccess(false), 3000);
      } else {
        setError(result.error || 'Failed to save configuration');
      }
    } catch (e) {
      setError(e instanceof Error ? e.message : 'Failed to save configuration');
    } finally {
      setSaving(false);
    }
  };

  const handleContextChange = (name: string, context: PddrcContext) => {
    if (!config) return;
    setConfig({
      ...config,
      contexts: {
        ...config.contexts,
        [name]: context,
      },
    });
  };

  const handleContextDelete = (name: string) => {
    if (!config || name === 'default') return;
    const newContexts = { ...config.contexts };
    delete newContexts[name];
    setConfig({ ...config, contexts: newContexts });
  };

  const handleContextRename = (oldName: string, newName: string) => {
    if (!config || oldName === 'default' || !newName || newName === oldName) return;
    if (config.contexts[newName]) {
      setError(`Context "${newName}" already exists`);
      return;
    }
    const newContexts: Record<string, PddrcContext> = {};
    for (const [key, value] of Object.entries(config.contexts) as [string, PddrcContext][]) {
      if (key === oldName) {
        newContexts[newName] = value;
      } else {
        newContexts[key] = value;
      }
    }
    setConfig({ ...config, contexts: newContexts });
  };

  const handleAddContext = () => {
    if (!config) return;
    let newName = 'new-context';
    let counter = 1;
    while (config.contexts[newName]) {
      newName = `new-context-${counter}`;
      counter++;
    }
    setConfig({
      ...config,
      contexts: {
        ...config.contexts,
        [newName]: {
          paths: [],
          defaults: {},
        },
      },
    });
  };

  if (loading) {
    return (
      <div className="flex flex-col items-center justify-center min-h-[400px] p-8 bg-surface-900/50 rounded-xl">
        <SpinnerIcon className="w-8 h-8 text-accent-400 animate-spin" />
        <p className="mt-4 text-surface-400 text-sm">Loading project settings...</p>
      </div>
    );
  }

  if (!config) {
    return (
      <div className="flex flex-col items-center justify-center min-h-[400px] p-8 gap-4">
        <p className="text-surface-400">Failed to load configuration</p>
        <button
          onClick={loadConfig}
          className="px-4 py-2 bg-accent-600 hover:bg-accent-500 text-white rounded-lg transition-colors"
        >
          Retry
        </button>
      </div>
    );
  }

  return (
    <div className="max-w-4xl mx-auto p-4 sm:p-6 lg:p-8 animate-fade-in">
      {/* Header */}
      <div className="flex flex-col sm:flex-row sm:items-center sm:justify-between gap-4 mb-6">
        <div className="flex items-center gap-3">
          <div className="w-10 h-10 rounded-xl bg-accent-500/20 flex items-center justify-center">
            <Cog6ToothIcon className="w-5 h-5 text-accent-400" />
          </div>
          <div>
            <h1 className="text-xl sm:text-2xl font-semibold text-white">Project Settings</h1>
            <p className="text-sm text-surface-400">Configure where your code, tests, and examples are saved</p>
          </div>
        </div>
        <button
          onClick={handleSave}
          disabled={saving || !hasChanges()}
          className={`px-4 py-2 rounded-xl font-medium transition-all flex items-center gap-2 ${
            saving || !hasChanges()
              ? 'bg-surface-700 text-surface-500 cursor-not-allowed'
              : saveSuccess
              ? 'bg-green-600 text-white'
              : 'bg-accent-600 hover:bg-accent-500 text-white'
          }`}
        >
          {saving ? (
            <>
              <SpinnerIcon className="w-4 h-4 animate-spin" />
              Saving...
            </>
          ) : saveSuccess ? (
            'Saved!'
          ) : (
            'Save Changes'
          )}
        </button>
      </div>

      {/* Error message */}
      {error && (
        <div className="mb-4 p-3 bg-red-500/20 border border-red-500/50 rounded-lg text-red-300 text-sm">
          {error}
        </div>
      )}

      {/* Description */}
      <div className="mb-6 p-4 glass rounded-xl border border-surface-700/50">
        <p className="text-sm text-surface-300">
          Define output paths for different parts of your project. Each <strong>context</strong> matches
          file patterns and applies specific settings. The <strong>default</strong> context matches all
          files not covered by other contexts.
        </p>
      </div>

      {/* Context list */}
      <div className="space-y-4">
        {config?.contexts &&
          Object.entries(config.contexts).map(([name, context]) => (
            <ContextCard
              key={name}
              name={name}
              context={context}
              isDefault={name === 'default'}
              onChange={handleContextChange}
              onDelete={handleContextDelete}
              onRename={handleContextRename}
            />
          ))}
      </div>

      {/* Add context button */}
      <button
        onClick={handleAddContext}
        className="mt-4 w-full px-4 py-3 border-2 border-dashed border-surface-600 rounded-xl text-surface-400 hover:text-white hover:border-accent-500 transition-colors flex items-center justify-center gap-2"
      >
        <PlusIcon className="w-5 h-5" />
        Add Context
      </button>

      {/* PDD Cloud Authentication Section */}
      <div className="mt-8 glass rounded-xl border border-surface-700/50 p-4 sm:p-6">
        <div className="flex items-center gap-3 mb-4">
          <div className="w-10 h-10 rounded-xl bg-blue-500/20 flex items-center justify-center">
            <svg className="w-5 h-5 text-blue-400" fill="none" stroke="currentColor" viewBox="0 0 24 24">
              <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M15 7a2 2 0 012 2m4 0a6 6 0 01-7.743 5.743L11 17H9v2H7v2H4a1 1 0 01-1-1v-2.586a1 1 0 01.293-.707l5.964-5.964A6 6 0 1121 9z" />
            </svg>
          </div>
          <div>
            <h2 className="text-lg font-semibold text-white">PDD Cloud Authentication</h2>
            <p className="text-sm text-surface-400">Manage your GitHub authentication for PDD Cloud</p>
          </div>
        </div>

        {/* Current Status */}
        <div className="flex items-center gap-3 p-3 rounded-lg bg-surface-800/50 mb-4">
          <div className={`w-3 h-3 rounded-full ${
            authStatus?.authenticated ? 'bg-green-400' : 'bg-yellow-400 animate-pulse'
          }`} />
          <div>
            <p className="text-sm font-medium text-white">
              {authStatus?.authenticated ? 'Currently Authenticated' : 'Not Authenticated'}
            </p>
            <p className="text-xs text-surface-400">
              {authStatus?.authenticated
                ? authStatus.cached
                  ? 'Using cached JWT token'
                  : 'Using refresh token'
                : 'No valid tokens found'}
            </p>
          </div>
        </div>

        <p className="text-sm text-surface-300 mb-4">
          Clear stored tokens to force a fresh GitHub Device Flow login on the next PDD command.
        </p>

        {authResult && (
          <div className={`mb-4 p-3 rounded-lg text-sm ${
            authResult.success
              ? 'bg-green-500/20 text-green-300 border border-green-500/30'
              : 'bg-red-500/20 text-red-300 border border-red-500/30'
          }`}>
            {authResult.message}
          </div>
        )}

        <button
          onClick={handleLogout}
          disabled={authLoading}
          className="px-4 py-2 bg-red-600/80 hover:bg-red-600 text-white rounded-lg transition-colors flex items-center gap-2 disabled:opacity-50"
        >
          {authLoading ? (
            <>
              <SpinnerIcon className="w-4 h-4 animate-spin" />
              Clearing...
            </>
          ) : (
            <>
              <svg className="w-4 h-4" fill="none" stroke="currentColor" viewBox="0 0 24 24">
                <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M4 4v5h.582m15.356 2A8.001 8.001 0 004.582 9m0 0H9m11 11v-5h-.581m0 0a8.003 8.003 0 01-15.357-2m15.357 2H15" />
              </svg>
              Force Re-authentication
            </>
          )}
        </button>
        <p className="mt-2 text-xs text-surface-500">
          Clears JWT cache (~/.pdd/jwt_cache) and refresh token from system keyring.
        </p>
      </div>

      {/* Unsaved changes warning */}
      {hasChanges() && (
        <div className="mt-4 p-3 bg-yellow-500/20 border border-yellow-500/50 rounded-lg text-yellow-300 text-sm">
          You have unsaved changes. Click "Save Changes" to persist your configuration.
        </div>
      )}
    </div>
  );
};

export default ProjectSettings;
