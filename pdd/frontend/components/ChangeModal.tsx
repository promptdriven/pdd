import React, { useState } from 'react';
import { SpinnerIcon } from './Icon';

type ModalState = 'input' | 'loading' | 'confirm' | 'error';

interface ChangeModalProps {
  onClose: () => void;
  onSubmit: (changeRequest: string) => void;
  onDetect: (changeRequest: string) => Promise<string>;
}

const ChangeModal: React.FC<ChangeModalProps> = ({ onClose, onSubmit, onDetect }) => {
  const [changeRequest, setChangeRequest] = useState('');
  const [modalState, setModalState] = useState<ModalState>('input');
  const [errorMessage, setErrorMessage] = useState('');
  const [suggestedFile, setSuggestedFile] = useState('');

  const handleDetectSubmit = async (e: React.FormEvent) => {
    e.preventDefault();
    if (!changeRequest.trim()) return;

    setModalState('loading');
    setErrorMessage('');

    try {
      const file = await onDetect(changeRequest.trim());
      setSuggestedFile(file);
      setModalState('confirm');
    } catch (error) {
      console.error(error);
      setErrorMessage(error instanceof Error ? error.message : 'An unknown error occurred.');
      setModalState('error');
    }
  };

  const handleConfirmSubmit = () => {
    onSubmit(changeRequest.trim());
  };

  const renderContent = () => {
    switch (modalState) {
      case 'loading':
        return (
          <div className="flex flex-col items-center justify-center p-10 space-y-4">
            <SpinnerIcon className="w-12 h-12 text-blue-500 animate-spin" />
            <p className="text-lg text-gray-300">Analyzing your request...</p>
            <p className="text-sm text-gray-400">The AI is identifying the best prompt to modify.</p>
          </div>
        );
      case 'confirm':
        return (
          <>
            <main className="p-6 space-y-4">
              <p className="text-sm text-gray-300">
                Based on your request, the AI suggests modifying the following prompt:
              </p>
              <div className="bg-gray-900/50 rounded-md p-4 text-center">
                <p className="font-mono text-lg text-blue-400">{suggestedFile}</p>
              </div>
              <p className="text-sm text-gray-300">
                Do you want to proceed with this suggestion? This will set up the <code className="bg-gray-700 px-1 py-0.5 rounded text-xs text-amber-400">pdd change</code> command for you in the builder.
              </p>
            </main>
            <footer className="px-6 py-4 bg-gray-800/50 border-t border-gray-700 flex justify-end space-x-3 rounded-b-lg">
              <button
                type="button"
                onClick={() => setModalState('input')}
                className="px-4 py-2 rounded-md text-sm font-medium bg-gray-600 text-white hover:bg-gray-700 focus:outline-none focus:ring-2 focus:ring-offset-2 focus:ring-offset-gray-800 focus:ring-gray-500 transition-colors"
              >
                Back
              </button>
              <button
                type="button"
                onClick={handleConfirmSubmit}
                className="px-4 py-2 rounded-md text-sm font-medium bg-blue-600 text-white hover:bg-blue-700 focus:outline-none focus:ring-2 focus:ring-offset-2 focus:ring-offset-gray-800 focus:ring-blue-500 transition-colors"
              >
                Confirm & Proceed
              </button>
            </footer>
          </>
        );
      case 'error':
        return (
          <>
            <main className="p-6 space-y-4">
              <p className="text-lg text-red-400 font-semibold">An Error Occurred</p>
              <div className="bg-red-900/50 rounded-md p-4 text-red-300 text-sm">
                <p>{errorMessage}</p>
              </div>
               <p className="text-sm text-gray-400">
                Please check your setup or try a different request.
              </p>
            </main>
            <footer className="px-6 py-4 bg-gray-800/50 border-t border-gray-700 flex justify-end space-x-3 rounded-b-lg">
              <button
                type="button"
                onClick={() => setModalState('input')}
                className="px-4 py-2 rounded-md text-sm font-medium bg-gray-600 text-white hover:bg-gray-700 focus:outline-none focus:ring-2 focus:ring-offset-2 focus:ring-offset-gray-800 focus:ring-gray-500 transition-colors"
              >
                Try Again
              </button>
            </footer>
          </>
        );
      case 'input':
      default:
        return (
          <form onSubmit={handleDetectSubmit}>
            <main className="p-6 space-y-4">
              <p className="text-sm text-gray-300">
                Describe the change you want to make in plain English. The AI will analyze your request and suggest which prompt file is the best one to modify.
              </p>
              <div>
                <label htmlFor="change-request" className="sr-only">
                  Change Request
                </label>
                <textarea
                  id="change-request"
                  name="change-request"
                  rows={5}
                  value={changeRequest}
                  onChange={e => setChangeRequest(e.target.value)}
                  placeholder="e.g., Add a loading spinner to the button component when it's in a submitting state."
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
                className="px-4 py-2 rounded-md text-sm font-medium bg-blue-600 text-white hover:bg-blue-700 focus:outline-none focus:ring-2 focus:ring-offset-2 focus:ring-offset-gray-800 focus:ring-blue-500 transition-colors disabled:opacity-50"
                disabled={!changeRequest.trim()}
              >
                Find Prompt
              </button>
            </footer>
          </form>
        );
    }
  };

  return (
    <div
      className="fixed inset-0 bg-black/60 flex items-center justify-center z-50 p-4 animate-fade-in"
      onClick={modalState !== 'loading' ? onClose : undefined}
      role="dialog"
      aria-modal="true"
      aria-labelledby="change-modal-title"
    >
      <div
        className="bg-gray-800 rounded-lg shadow-xl w-full max-w-lg flex flex-col ring-1 ring-white/10"
        onClick={e => e.stopPropagation()}
      >
        <header className="flex items-center justify-between p-4 border-b border-gray-700">
          <h2 id="change-modal-title" className="text-lg font-semibold text-white">
            Propose a Change
          </h2>
          <button
            onClick={onClose}
            className="p-2 rounded-full text-gray-400 hover:bg-gray-700 hover:text-white transition-colors focus:outline-none focus:ring-2 focus:ring-blue-500 disabled:opacity-50"
            aria-label="Close modal"
            disabled={modalState === 'loading'}
          >
            <svg xmlns="http://www.w3.org/2000/svg" className="h-6 w-6" fill="none" viewBox="0 0 24 24" stroke="currentColor">
              <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M6 18L18 6M6 6l12 12" />
            </svg>
          </button>
        </header>
        {renderContent()}
      </div>
    </div>
  );
};

export default ChangeModal;