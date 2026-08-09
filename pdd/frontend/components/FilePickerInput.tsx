import React, { useState } from 'react';
import FileBrowser from './FileBrowser';
import { FolderOpenIcon } from './Icon';

interface FilePickerInputProps {
  label: string;
  value: string;
  onChange: (path: string) => void;
  placeholder?: string;
  description?: string;
  required?: boolean;
  filter?: string | string[];
  directoryMode?: boolean;
  title?: string;
  isDetected?: boolean;
  detectedLabel?: string;
  className?: string;
}

/**
 * A reusable file input component with integrated file browser.
 * Combines a text input with a browse button that opens FileBrowser modal.
 */
const FilePickerInput: React.FC<FilePickerInputProps> = ({
  label,
  value,
  onChange,
  placeholder = '',
  description,
  required = false,
  filter,
  directoryMode = false,
  title,
  isDetected,
  detectedLabel = 'detected',
  className = '',
}) => {
  const [showBrowser, setShowBrowser] = useState(false);

  const handleSelect = (path: string) => {
    onChange(path);
    setShowBrowser(false);
  };

  const handleInputChange = (e: React.ChangeEvent<HTMLInputElement>) => {
    onChange(e.target.value);
  };

  // Determine border color based on detection status
  const borderClass = isDetected !== undefined
    ? (isDetected ? 'border-green-500/50' : 'border-yellow-500/50')
    : 'border-surface-600';

  return (
    <div className={className}>
      <label className="block text-sm font-medium text-white mb-1.5">
        {label}
        {required && <span className="text-red-400 ml-1">*</span>}
      </label>
      {description && (
        <p className="text-xs text-surface-400 mb-2">{description}</p>
      )}
      <div className="relative flex gap-2">
        <div className="relative flex-1">
          <input
            type="text"
            value={value}
            onChange={handleInputChange}
            placeholder={placeholder}
            className={`w-full px-3 py-2.5 bg-surface-900/50 border ${borderClass} rounded-xl text-white placeholder-surface-500 focus:outline-none focus:border-accent-500 focus:ring-1 focus:ring-accent-500/50 text-sm transition-all pr-20`}
          />
          {isDetected && (
            <span className="absolute right-3 top-1/2 -translate-y-1/2 text-green-400 text-xs px-1.5 py-0.5 rounded bg-green-500/20">
              {detectedLabel}
            </span>
          )}
        </div>
        <button
          type="button"
          onClick={() => setShowBrowser(true)}
          className="px-3 py-2.5 bg-surface-700 hover:bg-surface-600 rounded-xl text-surface-300 hover:text-white transition-colors flex items-center gap-2"
          title="Browse files"
        >
          <FolderOpenIcon className="w-4 h-4" />
        </button>
      </div>

      {showBrowser && (
        <FileBrowser
          onSelect={handleSelect}
          onClose={() => setShowBrowser(false)}
          filter={filter}
          directoryMode={directoryMode}
          title={title || (directoryMode ? 'Select Directory' : 'Select File')}
        />
      )}
    </div>
  );
};

export default FilePickerInput;
