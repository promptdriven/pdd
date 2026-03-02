import React, { useState, useEffect, useMemo } from 'react';
import { ArchitectureModule } from '../api';

interface GroupEditModalProps {
  isOpen: boolean;
  groupName: string | null;  // null = create new group
  allModules: ArchitectureModule[];
  onSave: (groupName: string, moduleFilenames: string[]) => void;
  onClose: () => void;
}

const GroupEditModal: React.FC<GroupEditModalProps> = ({
  isOpen,
  groupName,
  allModules,
  onSave,
  onClose,
}) => {
  const [name, setName] = useState('');
  const [selectedFilenames, setSelectedFilenames] = useState<Set<string>>(new Set());

  const existingGroups = useMemo(() => {
    const groups = new Set<string>();
    allModules.forEach(m => { if (m.group) groups.add(m.group); });
    return Array.from(groups).sort();
  }, [allModules]);

  useEffect(() => {
    if (isOpen) {
      if (groupName) {
        setName(groupName);
        setSelectedFilenames(new Set(allModules.filter(m => m.group === groupName).map(m => m.filename)));
      } else {
        setName('');
        setSelectedFilenames(new Set());
      }
    }
  }, [isOpen, groupName, allModules]);

  const toggleModule = (filename: string) => {
    setSelectedFilenames(prev => {
      const next = new Set(prev);
      if (next.has(filename)) {
        next.delete(filename);
      } else {
        next.add(filename);
      }
      return next;
    });
  };

  const handleSave = () => {
    const trimmedName = name.trim();
    if (!trimmedName) return;
    onSave(trimmedName, Array.from(selectedFilenames));
    onClose();
  };

  if (!isOpen) return null;

  return (
    <div className="fixed inset-0 z-50 flex items-center justify-center bg-black/60 backdrop-blur-sm">
      <div className="glass rounded-2xl border border-surface-700/50 w-full max-w-lg mx-4 shadow-2xl">
        <div className="p-6">
          <div className="flex items-center justify-between mb-6">
            <h2 className="text-lg font-semibold text-white">
              {groupName ? 'Edit Group' : 'Create Group'}
            </h2>
            <button
              onClick={onClose}
              className="p-2 hover:bg-surface-700 rounded-lg transition-colors text-surface-400 hover:text-white"
            >
              <svg className="w-5 h-5" fill="none" stroke="currentColor" viewBox="0 0 24 24">
                <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M6 18L18 6M6 6l12 12" />
              </svg>
            </button>
          </div>

          <div className="mb-4">
            <label className="block text-xs font-medium text-surface-400 uppercase tracking-wider mb-2">
              Group Name
            </label>
            <input
              type="text"
              value={name}
              onChange={e => setName(e.target.value)}
              placeholder="e.g. Auth, Orders, API"
              className="w-full px-3 py-2 bg-surface-900/50 border border-surface-600 rounded-lg text-sm text-white placeholder-surface-500 focus:outline-none focus:border-accent-500"
              autoFocus
              list="group-edit-existing"
              onKeyDown={e => { if (e.key === 'Enter') handleSave(); }}
            />
            {existingGroups.length > 0 && (
              <datalist id="group-edit-existing">
                {existingGroups.map(g => <option key={g} value={g} />)}
              </datalist>
            )}
          </div>

          <div className="mb-6">
            <label className="block text-xs font-medium text-surface-400 uppercase tracking-wider mb-2">
              Modules in this group ({selectedFilenames.size} selected)
            </label>
            <div className="space-y-1 max-h-60 overflow-y-auto pr-1">
              {allModules.map(m => (
                <label
                  key={m.filename}
                  className="flex items-center gap-3 p-2 rounded-lg hover:bg-surface-800/50 cursor-pointer"
                >
                  <input
                    type="checkbox"
                    checked={selectedFilenames.has(m.filename)}
                    onChange={() => toggleModule(m.filename)}
                    className="w-4 h-4 rounded border-surface-600 bg-surface-900 text-accent-500 focus:ring-accent-500"
                  />
                  <div className="flex-1 min-w-0">
                    <p className="text-sm text-white truncate font-mono">
                      {m.filename.replace(/\.prompt$/, '')}
                    </p>
                    {m.group && m.group !== name.trim() && (
                      <p className="text-[10px] text-yellow-500 truncate">Currently in: {m.group}</p>
                    )}
                  </div>
                </label>
              ))}
            </div>
          </div>

          <div className="flex gap-3 justify-end">
            <button
              onClick={onClose}
              className="px-4 py-2 rounded-lg text-sm text-surface-300 hover:text-white bg-surface-700 hover:bg-surface-600 transition-colors"
            >
              Cancel
            </button>
            <button
              onClick={handleSave}
              disabled={!name.trim()}
              className="px-4 py-2 rounded-lg text-sm font-medium bg-accent-600 hover:bg-accent-500 text-white disabled:opacity-50 disabled:cursor-not-allowed transition-colors"
            >
              Save Group
            </button>
          </div>
        </div>
      </div>
    </div>
  );
};

export default GroupEditModal;
