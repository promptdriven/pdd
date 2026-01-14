import React, { useState, useMemo } from 'react';
import { SUPPORTED_LANGUAGES, getPromptTemplate } from '../constants';
import { PromptInfo } from '../api';

interface CreatePromptModalProps {
  onClose: () => void;
  onCreate: (promptInfo: { path: string; content: string; info: PromptInfo }) => Promise<void>;
  isCreating: boolean;
  existingPrompts: PromptInfo[];
}

// Validation function for prompt names
const validatePromptName = (name: string): string | null => {
  if (!name.trim()) return 'Name is required';
  if (name.length < 2) return 'Name must be at least 2 characters';
  if (name.length > 50) return 'Name must be 50 characters or less';
  if (!/^[a-z][a-z0-9_]*$/.test(name)) {
    return 'Name must start with a letter and contain only lowercase letters, numbers, and underscores';
  }
  return null;
};

const CreatePromptModal: React.FC<CreatePromptModalProps> = ({
  onClose,
  onCreate,
  isCreating,
  existingPrompts,
}) => {
  const [name, setName] = useState('');
  const [language, setLanguage] = useState('python');
  const [description, setDescription] = useState('');
  const [error, setError] = useState<string | null>(null);

  // Generate the filename preview
  const filename = useMemo(() => {
    if (!name.trim()) return '';
    return `prompts/${name.trim()}_${language}.prompt`;
  }, [name, language]);

  // Check for duplicates
  const isDuplicate = useMemo(() => {
    if (!filename) return false;
    return existingPrompts.some(p => p.prompt === filename);
  }, [filename, existingPrompts]);

  // Validate on submit
  const handleSubmit = async (e: React.FormEvent) => {
    e.preventDefault();
    setError(null);

    const nameError = validatePromptName(name.trim());
    if (nameError) {
      setError(nameError);
      return;
    }

    if (isDuplicate) {
      setError('A prompt with this name and language already exists');
      return;
    }

    const content = getPromptTemplate(name.trim(), language, description);
    const promptInfo: PromptInfo = {
      prompt: filename,
      sync_basename: name.trim(),
      language,
    };

    try {
      await onCreate({ path: filename, content, info: promptInfo });
    } catch (err: any) {
      setError(err.message || 'Failed to create prompt');
    }
  };

  return (
    <div
      className="fixed inset-0 bg-black/60 flex items-center justify-center z-50 p-4 animate-fade-in"
      onClick={!isCreating ? onClose : undefined}
      role="dialog"
      aria-modal="true"
      aria-labelledby="create-prompt-title"
    >
      <div
        className="bg-gray-800 rounded-none sm:rounded-lg shadow-xl w-full h-full sm:h-auto sm:max-w-lg sm:max-h-[90vh] flex flex-col ring-1 ring-white/10 overflow-y-auto"
        onClick={e => e.stopPropagation()}
      >
        <header className="flex items-center justify-between p-4 border-b border-gray-700">
          <h2 id="create-prompt-title" className="text-lg font-semibold text-white">
            Create New Prompt
          </h2>
          <button
            onClick={onClose}
            className="p-2 rounded-full text-gray-400 hover:bg-gray-700 hover:text-white transition-colors focus:outline-none focus:ring-2 focus:ring-blue-500 disabled:opacity-50"
            aria-label="Close modal"
            disabled={isCreating}
          >
            <svg xmlns="http://www.w3.org/2000/svg" className="h-6 w-6" fill="none" viewBox="0 0 24 24" stroke="currentColor">
              <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M6 18L18 6M6 6l12 12" />
            </svg>
          </button>
        </header>

        <form onSubmit={handleSubmit}>
          <main className="p-6 space-y-4">
            {/* Name Field */}
            <div>
              <label htmlFor="prompt-name" className="block text-sm font-medium text-gray-300 mb-1.5">
                Prompt Name <span className="text-red-400">*</span>
              </label>
              <input
                id="prompt-name"
                type="text"
                value={name}
                onChange={e => setName(e.target.value.toLowerCase().replace(/[^a-z0-9_]/g, ''))}
                placeholder="calculator"
                className="block w-full rounded-md border-0 bg-white/5 py-2.5 px-3 text-white shadow-sm ring-1 ring-inset ring-white/10 focus:ring-2 focus:ring-inset focus:ring-blue-500 sm:text-sm transition-shadow duration-200"
                disabled={isCreating}
                autoFocus
              />
              <p className="mt-1 text-xs text-gray-500">
                Lowercase letters, numbers, and underscores only
              </p>
            </div>

            {/* Language Field */}
            <div>
              <label htmlFor="prompt-language" className="block text-sm font-medium text-gray-300 mb-1.5">
                Language <span className="text-red-400">*</span>
              </label>
              <select
                id="prompt-language"
                value={language}
                onChange={e => setLanguage(e.target.value)}
                className="block w-full rounded-md border-0 bg-white/5 py-2.5 px-3 text-white shadow-sm ring-1 ring-inset ring-white/10 focus:ring-2 focus:ring-inset focus:ring-blue-500 sm:text-sm transition-shadow duration-200"
                disabled={isCreating}
              >
                {SUPPORTED_LANGUAGES.map(lang => (
                  <option key={lang.value} value={lang.value} className="bg-gray-800">
                    {lang.label}
                  </option>
                ))}
              </select>
            </div>

            {/* Description Field */}
            <div>
              <label htmlFor="prompt-description" className="block text-sm font-medium text-gray-300 mb-1.5">
                Description <span className="text-gray-500">(optional)</span>
              </label>
              <textarea
                id="prompt-description"
                value={description}
                onChange={e => setDescription(e.target.value)}
                placeholder="handles basic arithmetic operations"
                rows={2}
                className="block w-full rounded-md border-0 bg-white/5 py-2.5 px-3 text-white shadow-sm ring-1 ring-inset ring-white/10 focus:ring-2 focus:ring-inset focus:ring-blue-500 sm:text-sm transition-shadow duration-200 resize-none"
                disabled={isCreating}
              />
              <p className="mt-1 text-xs text-gray-500">
                Brief description - will be included in the prompt template
              </p>
            </div>

            {/* Filename Preview */}
            {filename && (
              <div className={`rounded-md p-3 ${isDuplicate ? 'bg-red-900/30 ring-1 ring-red-500/30' : 'bg-gray-900/50'}`}>
                <p className="text-xs text-gray-400 mb-1">File will be created at:</p>
                <p className={`font-mono text-sm ${isDuplicate ? 'text-red-400' : 'text-blue-400'}`}>
                  {filename}
                </p>
                {isDuplicate && (
                  <p className="text-xs text-red-400 mt-1">
                    A prompt with this name already exists
                  </p>
                )}
              </div>
            )}

            {/* Error Message */}
            {error && (
              <div className="bg-red-900/30 rounded-md p-3 ring-1 ring-red-500/30">
                <p className="text-sm text-red-400">{error}</p>
              </div>
            )}
          </main>

          <footer className="px-6 py-4 bg-gray-800/50 border-t border-gray-700 flex justify-end space-x-3 rounded-b-lg">
            <button
              type="button"
              onClick={onClose}
              className="px-4 py-2 rounded-md text-sm font-medium bg-gray-600 text-white hover:bg-gray-700 focus:outline-none focus:ring-2 focus:ring-offset-2 focus:ring-offset-gray-800 focus:ring-gray-500 transition-colors disabled:opacity-50"
              disabled={isCreating}
            >
              Cancel
            </button>
            <button
              type="submit"
              className="px-4 py-2 rounded-md text-sm font-medium bg-blue-600 text-white hover:bg-blue-700 focus:outline-none focus:ring-2 focus:ring-offset-2 focus:ring-offset-gray-800 focus:ring-blue-500 transition-colors disabled:opacity-50 flex items-center gap-2"
              disabled={isCreating || !name.trim() || isDuplicate}
            >
              {isCreating ? (
                <>
                  <svg className="animate-spin h-4 w-4" viewBox="0 0 24 24">
                    <circle className="opacity-25" cx="12" cy="12" r="10" stroke="currentColor" strokeWidth="4" fill="none" />
                    <path className="opacity-75" fill="currentColor" d="M4 12a8 8 0 018-8V0C5.373 0 0 5.373 0 12h4z" />
                  </svg>
                  <span>Creating...</span>
                </>
              ) : (
                <span>Create & Edit</span>
              )}
            </button>
          </footer>
        </form>
      </div>
    </div>
  );
};

export default CreatePromptModal;
