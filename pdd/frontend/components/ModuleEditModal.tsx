import React, { useState, useEffect, useMemo } from 'react';
import { ArchitectureModule } from '../api';
import FilePickerInput from './FilePickerInput';

interface ModuleEditModalProps {
  isOpen: boolean;
  module: ArchitectureModule | null;
  allModules: ArchitectureModule[];
  onSave: (updatedModule: ArchitectureModule) => void;
  onDelete: (filename: string) => void;
  onClose: () => void;
}

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

const ModuleEditModal: React.FC<ModuleEditModalProps> = ({
  isOpen,
  module,
  allModules,
  onSave,
  onDelete,
  onClose,
}) => {
  const [filename, setFilename] = useState('');
  const [filepath, setFilepath] = useState('');
  const [description, setDescription] = useState('');
  const [reason, setReason] = useState('');
  const [priority, setPriority] = useState(5);
  const [tags, setTags] = useState('');
  const [group, setGroup] = useState('');
  const [interfaceType, setInterfaceType] = useState('module');
  const [dependencies, setDependencies] = useState<string[]>([]);
  const [showDeleteConfirm, setShowDeleteConfirm] = useState(false);

  // Available modules for dependencies (exclude self)
  const availableModules = useMemo(() => {
    return allModules.filter((m) => m.filename !== module?.filename);
  }, [allModules, module]);

  // Existing group names for autocomplete
  const existingGroups = useMemo(() => {
    const groups = new Set<string>();
    allModules.forEach(m => { if (m.group) groups.add(m.group); });
    return Array.from(groups).sort();
  }, [allModules]);

  // Initialize form when module changes
  useEffect(() => {
    if (module) {
      setFilename(module.filename);
      setFilepath(module.filepath);
      setDescription(module.description);
      setReason(module.reason);
      setPriority(module.priority);
      setTags(module.tags?.join(', ') || '');
      setGroup(module.group || '');
      setInterfaceType(module.interface?.type || 'module');
      setDependencies(module.dependencies || []);
      setShowDeleteConfirm(false);
    }
  }, [module]);

  // Validation
  const errors = useMemo(() => {
    const errs: string[] = [];
    if (!filename.trim()) errs.push('Filename is required');
    if (!filepath.trim()) errs.push('Filepath is required');
    if (!description.trim()) errs.push('Description is required');
    // Check for duplicate filename (if changed)
    if (module && filename !== module.filename) {
      if (allModules.some((m) => m.filename === filename)) {
        errs.push('Filename already exists');
      }
    }
    return errs;
  }, [filename, filepath, description, module, allModules]);

  const handleSave = () => {
    if (errors.length > 0) return;

    const updatedModule: ArchitectureModule = {
      filename,
      filepath,
      description,
      reason,
      priority,
      tags: tags
        .split(',')
        .map((t) => t.trim())
        .filter((t) => t),
      group: group.trim() || undefined,
      dependencies,
      interface: {
        type: interfaceType,
      },
    };
    onSave(updatedModule);
    onClose();
  };

  const handleDelete = () => {
    if (module) {
      onDelete(module.filename);
      onClose();
    }
  };

  const toggleDependency = (dep: string) => {
    setDependencies((prev) =>
      prev.includes(dep) ? prev.filter((d) => d !== dep) : [...prev, dep]
    );
  };

  if (!isOpen || !module) return null;

  return (
    <div className="fixed inset-0 bg-black/60 flex items-center justify-center z-50 p-4">
      <div className="bg-surface-800 rounded-none sm:rounded-xl border-0 sm:border border-surface-700 w-full h-full sm:h-auto sm:max-w-2xl sm:max-h-[90vh] overflow-hidden flex flex-col">
        {/* Header */}
        <div className="flex items-center justify-between px-6 py-4 border-b border-surface-700">
          <h2 className="text-lg font-semibold text-white">Edit Module</h2>
          <button
            onClick={onClose}
            className="p-1.5 rounded-lg hover:bg-surface-700 transition-colors"
          >
            <svg className="w-5 h-5 text-surface-400" fill="none" stroke="currentColor" viewBox="0 0 24 24">
              <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M6 18L18 6M6 6l12 12" />
            </svg>
          </button>
        </div>

        {/* Content */}
        <div className="flex-1 overflow-y-auto px-6 py-4 space-y-4">
          {/* Filename */}
          <div>
            <label className="block text-sm font-medium text-surface-300 mb-1">
              Filename <span className="text-red-400">*</span>
            </label>
            <input
              type="text"
              value={filename}
              onChange={(e) => setFilename(e.target.value)}
              placeholder="e.g., user_api_Python.prompt"
              className="w-full px-3 py-2 bg-surface-900 border border-surface-700 rounded-lg text-white placeholder-surface-500 focus:outline-none focus:ring-2 focus:ring-accent-500 text-sm"
            />
          </div>

          {/* Filepath */}
          <FilePickerInput
            label="Filepath"
            value={filepath}
            onChange={setFilepath}
            placeholder="e.g., src/api/user.py"
            description="Target path for the generated code"
            required
            title="Select Output Path"
          />

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

          {/* Reason */}
          <div>
            <label className="block text-sm font-medium text-surface-300 mb-1">Reason</label>
            <input
              type="text"
              value={reason}
              onChange={(e) => setReason(e.target.value)}
              placeholder="Why is this module needed?"
              className="w-full px-3 py-2 bg-surface-900 border border-surface-700 rounded-lg text-white placeholder-surface-500 focus:outline-none focus:ring-2 focus:ring-accent-500 text-sm"
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

          {/* Group */}
          <div>
            <label className="block text-sm font-medium text-surface-300 mb-1">
              Group <span className="text-surface-500">(optional, for graph layout)</span>
            </label>
            <input
              type="text"
              value={group}
              onChange={(e) => setGroup(e.target.value)}
              placeholder="e.g., Auth, Orders, API"
              className="w-full px-3 py-2 bg-surface-900 border border-surface-700 rounded-lg text-white placeholder-surface-500 focus:outline-none focus:ring-2 focus:ring-accent-500 text-sm"
              list="module-edit-groups"
            />
            {existingGroups.length > 0 && (
              <datalist id="module-edit-groups">
                {existingGroups.map(g => <option key={g} value={g} />)}
              </datalist>
            )}
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
          <div>
            <label className="block text-sm font-medium text-surface-300 mb-2">
              Dependencies <span className="text-surface-500">({dependencies.length} selected)</span>
            </label>
            <div className="bg-surface-900 border border-surface-700 rounded-lg p-2 max-h-40 overflow-y-auto">
              {availableModules.length === 0 ? (
                <p className="text-sm text-surface-500 text-center py-2">No other modules available</p>
              ) : (
                <div className="space-y-1">
                  {availableModules.map((m) => (
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
              )}
            </div>
          </div>

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
        <div className="flex items-center justify-between px-6 py-4 border-t border-surface-700 bg-surface-800/50">
          <div>
            {!showDeleteConfirm ? (
              <button
                onClick={() => setShowDeleteConfirm(true)}
                className="flex items-center gap-1.5 px-3 py-1.5 rounded-lg text-xs font-medium text-red-400 hover:bg-red-500/10 transition-colors"
              >
                <svg className="w-3.5 h-3.5" fill="none" stroke="currentColor" viewBox="0 0 24 24">
                  <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M19 7l-.867 12.142A2 2 0 0116.138 21H7.862a2 2 0 01-1.995-1.858L5 7m5 4v6m4-6v6m1-10V4a1 1 0 00-1-1h-4a1 1 0 00-1 1v3M4 7h16" />
                </svg>
                Delete Module
              </button>
            ) : (
              <div className="flex items-center gap-2">
                <span className="text-xs text-red-400">Are you sure?</span>
                <button
                  onClick={handleDelete}
                  className="px-2 py-1 rounded text-xs font-medium bg-red-600 text-white hover:bg-red-500 transition-colors"
                >
                  Yes, delete
                </button>
                <button
                  onClick={() => setShowDeleteConfirm(false)}
                  className="px-2 py-1 rounded text-xs font-medium bg-surface-700 text-surface-300 hover:bg-surface-600 transition-colors"
                >
                  Cancel
                </button>
              </div>
            )}
          </div>
          <div className="flex items-center gap-2">
            <button
              onClick={onClose}
              className="px-4 py-2 rounded-lg text-sm font-medium bg-surface-700 text-surface-300 hover:bg-surface-600 transition-colors"
            >
              Cancel
            </button>
            <button
              onClick={handleSave}
              disabled={errors.length > 0}
              className="px-4 py-2 rounded-lg text-sm font-medium bg-accent-600 text-white hover:bg-accent-500 disabled:opacity-50 disabled:cursor-not-allowed transition-colors"
            >
              Save Changes
            </button>
          </div>
        </div>
      </div>
    </div>
  );
};

export default ModuleEditModal;
