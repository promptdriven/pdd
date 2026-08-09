import React, { useState } from 'react';

interface BugModalProps {
  onClose: () => void;
  onSubmit: (bugDescription: string) => void;
}

const BugModal: React.FC<BugModalProps> = ({ onClose, onSubmit }) => {
  const [bugDescription, setBugDescription] = useState('');

  const handleSubmit = (e: React.FormEvent) => {
    e.preventDefault();
    if (!bugDescription.trim()) return;
    onSubmit(bugDescription.trim());
  };

  return (
    <div
      className="fixed inset-0 bg-black/60 flex items-center justify-center z-50 p-4 animate-fade-in"
      onClick={onClose}
      role="dialog"
      aria-modal="true"
      aria-labelledby="bug-modal-title"
    >
      <div
        className="bg-gray-800 rounded-lg shadow-xl w-full max-w-lg flex flex-col ring-1 ring-white/10"
        onClick={e => e.stopPropagation()}
      >
        <header className="flex items-center justify-between p-4 border-b border-gray-700">
          <h2 id="bug-modal-title" className="text-lg font-semibold text-white">
            Report a Bug
          </h2>
          <button
            onClick={onClose}
            className="p-2 rounded-full text-gray-400 hover:bg-gray-700 hover:text-white transition-colors focus:outline-none focus:ring-2 focus:ring-blue-500"
            aria-label="Close modal"
          >
            <svg xmlns="http://www.w3.org/2000/svg" className="h-6 w-6" fill="none" viewBox="0 0 24 24" stroke="currentColor">
              <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M6 18L18 6M6 6l12 12" />
            </svg>
          </button>
        </header>
        <form onSubmit={handleSubmit}>
          <main className="p-6 space-y-4">
            <p className="text-sm text-gray-300">
              Describe the bug you've encountered in plain English. The AI will use this description and the current prompt's context to generate a test case that reproduces the bug.
            </p>
            <div>
              <label htmlFor="bug-description" className="sr-only">
                Bug Description
              </label>
              <textarea
                id="bug-description"
                name="bug-description"
                rows={5}
                value={bugDescription}
                onChange={e => setBugDescription(e.target.value)}
                placeholder="e.g., The button stays disabled even after the form is submitted successfully."
                className="block w-full rounded-md border-0 bg-white/5 py-2 px-3 text-white shadow-sm ring-1 ring-inset ring-white/10 focus:ring-2 focus:ring-inset focus:ring-blue-500 sm:text-sm sm:leading-6 transition-shadow duration-200"
                required
              />
            </div>
          </main>
          <footer className="px-6 py-4 bg-gray-800/50 border-t border-gray-700 flex justify-end space-x-3 rounded-b-lg">
            <button
              type="button"
              onClick={onClose}
              className="px-4 py-2 rounded-md text-sm font-medium bg-gray-600 text-white hover:bg-gray-700 focus:outline-none focus:ring-2 focus:ring-offset-2 focus:ring-offset-gray-800 focus:ring-gray-500 transition-colors"
            >
              Cancel
            </button>
            <button
              type="submit"
              className="px-4 py-2 rounded-md text-sm font-medium bg-red-600 text-white hover:bg-red-700 focus:outline-none focus:ring-2 focus:ring-offset-2 focus:ring-offset-gray-800 focus:ring-red-500 transition-colors disabled:opacity-50"
              disabled={!bugDescription.trim()}
            >
              Generate Test Case
            </button>
          </footer>
        </form>
      </div>
    </div>
  );
};

export default BugModal;