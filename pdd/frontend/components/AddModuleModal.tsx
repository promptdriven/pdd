import React, { useState, useMemo } from 'react';
import { ArchitectureModule } from '../api';
import FilePickerInput from './FilePickerInput';

interface AddModuleModalProps {
  isOpen: boolean;
  existingModules: ArchitectureModule[];
  onAdd: (newModule: ArchitectureModule) => void;
  onClose: () => void;
}

const LANGUAGES = [
  'Python',
  'TypeScript',
  'JavaScript',
  'Java',
  'Go',
  'Rust',
  'Ruby',
  'C++',
] as const;

const INTERFACE_TYPES = [
  'module',
  'component',
  'page',
  'api',
  'graphql',
  'cli',
  'job',
  'message',
  'config',
] as const;

const AddModuleModal: React.FC<AddModuleModalProps> = ({
  isOpen,
  existingModules,
  onAdd,
  onClose,
}) => {
  const [moduleName, setModuleName] = useState('');
  const [language, setLanguage] = useState<(typeof LANGUAGES)[number]>('Python');
  const [filepath, setFilepath] = useState('');
  const [description, setDescription] = useState('');
  const [reason, setReason] = useState('');
  const [priority, setPriority] = useState(5);
  const [tags, setTags] = useState('');
  const [interfaceType, setInterfaceType] = useState('module');
  const [dependencies, setDependencies] = useState<string[]>([]);

  // Auto-generate filename
  const filename = useMemo(() => {
    if (!moduleName.trim()) return '';
    const sanitized = moduleName.trim().toLowerCase().replace(/\s+/g, '_');
    return `${sanitized}_${language}.prompt`;
  }, [moduleName, language]);

  // Auto-suggest filepath based on language and interface type
  const suggestedFilepath = useMemo(() => {
    if (!moduleName.trim()) return '';
    const sanitized = moduleName.trim().toLowerCase().replace(/\s+/g, '_');
    const ext = language === 'Python' ? 'py' : language === 'TypeScript' || language === 'JavaScript' ? 'ts' : language.toLowerCase();
    const prefix = interfaceType === 'api' ? 'src/api/' : interfaceType === 'component' ? 'src/components/' : interfaceType === 'page' ? 'src/pages/' : 'src/';
    return `${prefix}${sanitized}.${ext}`;
  }, [moduleName, language, interfaceType]);

  // Use suggested filepath if filepath is empty
  const effectiveFilepath = filepath || suggestedFilepath;

  // Validation
  const errors = useMemo(() => {
    const errs: string[] = [];
    if (!moduleName.trim()) errs.push('Module name is required');
    if (!description.trim()) errs.push('Description is required');
    if (existingModules.some((m) => m.filename === filename)) {
      errs.push('A module with this name and language already exists');
    }
    return errs;
  }, [moduleName, description, filename, existingModules]);

  const handleAdd = () => {
    if (errors.length > 0) return;

    const newModule: ArchitectureModule = {
      filename,
      filepath: effectiveFilepath,
      description,
      reason: reason || `Module for ${moduleName}`,
      priority,
      tags: tags
        .split(',')
        .map((t) => t.trim())
        .filter((t) => t),
      dependencies,
      interface: {
        type: interfaceType,
      },
    };
    onAdd(newModule);
    resetForm();
    onClose();
  };

  const resetForm = () => {
    setModuleName('');
    setLanguage('Python');
    setFilepath('');
    setDescription('');
    setReason('');
    setPriority(5);
    setTags('');
    setInterfaceType('module');
    setDependencies([]);
  };

  const handleClose = () => {
    resetForm();
    onClose();
  };

  const toggleDependency = (dep: string) => {
    setDependencies((prev) =>
      prev.includes(dep) ? prev.filter((d) => d !== dep) : [...prev, dep]
    );
  };

  if (!isOpen) return null;

  return (
    <div className="fixed inset-0 bg-black/60 flex items-center justify-center z-50 p-4">
      <div className="bg-surface-800 rounded-none sm:rounded-xl border-0 sm:border border-surface-700 w-full h-full sm:h-auto sm:max-w-2xl sm:max-h-[90vh] overflow-hidden flex flex-col">
        {/* Header */}
        <div className="flex items-center justify-between px-6 py-4 border-b border-surface-700">
          <h2 className="text-lg font-semibold text-white">Add New Module</h2>
          <button
            onClick={handleClose}
            className="p-1.5 rounded-lg hover:bg-surface-700 transition-colors"
          >
            <svg className="w-5 h-5 text-surface-400" fill="none" stroke="currentColor" viewBox="0 0 24 24">
              <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M6 18L18 6M6 6l12 12" />
            </svg>
          </button>
        </div>

        {/* Content */}
        <div className="flex-1 overflow-y-auto px-6 py-4 space-y-4">
          {/* Module Name and Language */}
          <div className="grid grid-cols-2 gap-4">
            <div>
              <label className="block text-sm font-medium text-surface-300 mb-1">
                Module Name <span className="text-red-400">*</span>
              </label>
              <input
                type="text"
                value={moduleName}
                onChange={(e) => setModuleName(e.target.value)}
                placeholder="e.g., user_api"
                className="w-full px-3 py-2 bg-surface-900 border border-surface-700 rounded-lg text-white placeholder-surface-500 focus:outline-none focus:ring-2 focus:ring-accent-500 text-sm"
                autoFocus
              />
            </div>
            <div>
              <label className="block text-sm font-medium text-surface-300 mb-1">Language</label>
              <select
                value={language}
                onChange={(e) => setLanguage(e.target.value as (typeof LANGUAGES)[number])}
                className="w-full px-3 py-2 bg-surface-900 border border-surface-700 rounded-lg text-white focus:outline-none focus:ring-2 focus:ring-accent-500 text-sm"
              >
                {LANGUAGES.map((lang) => (
                  <option key={lang} value={lang}>
                    {lang}
                  </option>
                ))}
              </select>
            </div>
          </div>

          {/* Auto-generated Filename */}
          {filename && (
            <div className="bg-surface-900/50 rounded-lg px-3 py-2">
              <span className="text-xs text-surface-500">Generated filename: </span>
              <span className="text-xs text-accent-400 font-mono">{filename}</span>
            </div>
          )}

          {/* Filepath */}
          <div>
            <FilePickerInput
              label="Filepath"
              value={filepath}
              onChange={setFilepath}
              placeholder={suggestedFilepath || 'e.g., src/api/user.py'}
              description="Target path for the generated code (auto-suggested based on name and type)"
              title="Select Output Path"
            />
            {!filepath && suggestedFilepath && (
              <p className="text-xs text-surface-500 mt-1">Will use: {suggestedFilepath}</p>
            )}
          </div>

          {/* Description */}
          <div>
            <label className="block text-sm font-medium text-surface-300 mb-1">
              Description <span className="text-red-400">*</span>
            </label>
            <textarea
              value={description}
              onChange={(e) => setDescription(e.target.value)}
              placeholder="What does this module do?"
              rows={3}
              className="w-full px-3 py-2 bg-surface-900 border border-surface-700 rounded-lg text-white placeholder-surface-500 focus:outline-none focus:ring-2 focus:ring-accent-500 text-sm resize-none"
            />
          </div>

          {/* Priority and Interface Type */}
          <div className="grid grid-cols-2 gap-4">
            <div>
              <label className="block text-sm font-medium text-surface-300 mb-1">Priority</label>
              <input
                type="number"
                value={priority}
                onChange={(e) => setPriority(parseInt(e.target.value) || 1)}
                min={1}
                max={10}
                className="w-full px-3 py-2 bg-surface-900 border border-surface-700 rounded-lg text-white focus:outline-none focus:ring-2 focus:ring-accent-500 text-sm"
              />
            </div>
            <div>
              <label className="block text-sm font-medium text-surface-300 mb-1">Interface Type</label>
              <select
                value={interfaceType}
                onChange={(e) => setInterfaceType(e.target.value)}
                className="w-full px-3 py-2 bg-surface-900 border border-surface-700 rounded-lg text-white focus:outline-none focus:ring-2 focus:ring-accent-500 text-sm"
              >
                {INTERFACE_TYPES.map((type) => (
                  <option key={type} value={type}>
                    {type}
                  </option>
                ))}
              </select>
            </div>
          </div>

          {/* Tags */}
          <div>
            <label className="block text-sm font-medium text-surface-300 mb-1">
              Tags <span className="text-surface-500">(comma-separated)</span>
            </label>
            <input
              type="text"
              value={tags}
              onChange={(e) => setTags(e.target.value)}
              placeholder="e.g., backend, api, python"
              className="w-full px-3 py-2 bg-surface-900 border border-surface-700 rounded-lg text-white placeholder-surface-500 focus:outline-none focus:ring-2 focus:ring-accent-500 text-sm"
            />
          </div>

          {/* Dependencies */}
          {existingModules.length > 0 && (
            <div>
              <label className="block text-sm font-medium text-surface-300 mb-2">
                Dependencies <span className="text-surface-500">({dependencies.length} selected)</span>
              </label>
              <div className="bg-surface-900 border border-surface-700 rounded-lg p-2 max-h-40 overflow-y-auto">
                <div className="space-y-1">
                  {existingModules.map((m) => (
                    <label
                      key={m.filename}
                      className="flex items-center gap-2 px-2 py-1.5 rounded hover:bg-surface-800 cursor-pointer"
                    >
                      <input
                        type="checkbox"
                        checked={dependencies.includes(m.filename)}
                        onChange={() => toggleDependency(m.filename)}
                        className="rounded border-surface-600 bg-surface-800 text-accent-500 focus:ring-accent-500"
                      />
                      <span className="text-sm text-surface-300 truncate">
                        {m.filename.replace(/_[A-Za-z]+\.prompt$/, '').replace(/\.prompt$/, '')}
                      </span>
                    </label>
                  ))}
                </div>
              </div>
            </div>
          )}

          {/* Validation errors */}
          {errors.length > 0 && (
            <div className="bg-red-500/10 border border-red-500/50 rounded-lg p-3">
              <ul className="text-sm text-red-400 space-y-1">
                {errors.map((err, i) => (
                  <li key={i} className="flex items-center gap-2">
                    <svg className="w-4 h-4 flex-shrink-0" fill="currentColor" viewBox="0 0 20 20">
                      <path fillRule="evenodd" d="M18 10a8 8 0 11-16 0 8 8 0 0116 0zm-7 4a1 1 0 11-2 0 1 1 0 012 0zm-1-9a1 1 0 00-1 1v4a1 1 0 102 0V6a1 1 0 00-1-1z" clipRule="evenodd" />
                    </svg>
                    {err}
                  </li>
                ))}
              </ul>
            </div>
          )}
        </div>

        {/* Footer */}
        <div className="flex items-center justify-end gap-2 px-6 py-4 border-t border-surface-700 bg-surface-800/50">
          <button
            onClick={handleClose}
            className="px-4 py-2 rounded-lg text-sm font-medium bg-surface-700 text-surface-300 hover:bg-surface-600 transition-colors"
          >
            Cancel
          </button>
          <button
            onClick={handleAdd}
            disabled={errors.length > 0}
            className="px-4 py-2 rounded-lg text-sm font-medium bg-emerald-600 text-white hover:bg-emerald-500 disabled:opacity-50 disabled:cursor-not-allowed transition-colors"
          >
            Add Module
          </button>
        </div>
      </div>
    </div>
  );
};

export default AddModuleModal;
