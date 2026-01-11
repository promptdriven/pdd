import React, { useState, useEffect } from 'react';
import { api, AuthStatus } from '../api';

interface ReauthModalProps {
  onClose: () => void;
}

const ReauthModal: React.FC<ReauthModalProps> = ({ onClose }) => {
  const [isLoggingOut, setIsLoggingOut] = useState(false);
  const [result, setResult] = useState<{ success: boolean; message: string } | null>(null);
  const [authStatus, setAuthStatus] = useState<AuthStatus | null>(null);

  useEffect(() => {
    const fetchStatus = async () => {
      try {
        const status = await api.getAuthStatus();
        setAuthStatus(status);
      } catch (e) {
        setAuthStatus({ authenticated: false, cached: false, expires_at: null });
      }
    };
    fetchStatus();
  }, []);

  const handleLogout = async () => {
    setIsLoggingOut(true);
    setResult(null);
    try {
      const res = await api.logout();
      if (res.success) {
        setResult({
          success: true,
          message: 'Tokens cleared successfully. Run any pdd command (e.g., pdd sync) to re-authenticate with GitHub.'
        });
        // Refresh auth status
        const newStatus = await api.getAuthStatus();
        setAuthStatus(newStatus);
      } else {
        setResult(res);
      }
    } catch (e) {
      setResult({
        success: false,
        message: e instanceof Error ? e.message : 'Failed to clear tokens'
      });
    } finally {
      setIsLoggingOut(false);
    }
  };

  return (
    <div
      className="fixed inset-0 bg-black/60 backdrop-blur-sm flex items-center justify-center z-50 p-4 animate-fade-in"
      onClick={onClose}
      role="dialog"
      aria-modal="true"
      aria-labelledby="reauth-modal-title"
    >
      <div
        className="bg-gray-800 rounded-lg shadow-xl w-full max-w-md flex flex-col ring-1 ring-white/10"
        onClick={e => e.stopPropagation()}
      >
        <header className="flex items-center justify-between p-4 border-b border-gray-700">
          <h2 id="reauth-modal-title" className="text-lg font-semibold text-white flex items-center gap-2">
            <svg className="w-5 h-5 text-blue-400" fill="none" stroke="currentColor" viewBox="0 0 24 24">
              <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M15 7a2 2 0 012 2m4 0a6 6 0 01-7.743 5.743L11 17H9v2H7v2H4a1 1 0 01-1-1v-2.586a1 1 0 01.293-.707l5.964-5.964A6 6 0 1121 9z" />
            </svg>
            PDD Cloud Authentication
          </h2>
          <button
            onClick={onClose}
            className="p-2 rounded-full text-gray-400 hover:bg-gray-700 hover:text-white transition-colors focus:outline-none focus:ring-2 focus:ring-blue-500"
            aria-label="Close modal"
          >
            <svg xmlns="http://www.w3.org/2000/svg" className="h-5 w-5" fill="none" viewBox="0 0 24 24" stroke="currentColor">
              <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M6 18L18 6M6 6l12 12" />
            </svg>
          </button>
        </header>

        <main className="p-6 space-y-4">
          {/* Current Status */}
          <div className="flex items-center gap-3 p-3 rounded-lg bg-gray-700/50">
            <div className={`w-3 h-3 rounded-full ${
              authStatus?.authenticated ? 'bg-green-400' : 'bg-yellow-400 animate-pulse'
            }`} />
            <div>
              <p className="text-sm font-medium text-white">
                {authStatus?.authenticated ? 'Currently Authenticated' : 'Not Authenticated'}
              </p>
              <p className="text-xs text-gray-400">
                {authStatus?.authenticated
                  ? authStatus.cached
                    ? 'Using cached JWT token'
                    : 'Using refresh token'
                  : 'No valid tokens found'}
              </p>
            </div>
          </div>

          <p className="text-sm text-gray-300">
            Clear stored tokens to force a fresh GitHub Device Flow login on the next PDD command.
          </p>

          <div className="text-xs text-gray-500 space-y-1">
            <p>This will clear:</p>
            <ul className="list-disc list-inside ml-2 space-y-0.5">
              <li>JWT cache (~/.pdd/jwt_cache)</li>
              <li>Refresh token from system keyring</li>
            </ul>
          </div>

          {result && (
            <div className={`p-3 rounded-lg text-sm ${
              result.success
                ? 'bg-green-500/20 text-green-300 border border-green-500/30'
                : 'bg-red-500/20 text-red-300 border border-red-500/30'
            }`}>
              {result.message}
            </div>
          )}
        </main>

        <footer className="px-6 py-4 bg-gray-800/50 border-t border-gray-700 flex justify-end gap-3 rounded-b-lg">
          <button
            type="button"
            onClick={onClose}
            className="px-4 py-2 rounded-md text-sm font-medium bg-gray-600 text-white hover:bg-gray-700 focus:outline-none focus:ring-2 focus:ring-offset-2 focus:ring-offset-gray-800 focus:ring-gray-500 transition-colors"
          >
            Close
          </button>
          <button
            onClick={handleLogout}
            disabled={isLoggingOut}
            className="px-4 py-2 rounded-md text-sm font-medium bg-red-600 text-white hover:bg-red-700 focus:outline-none focus:ring-2 focus:ring-offset-2 focus:ring-offset-gray-800 focus:ring-red-500 transition-colors disabled:opacity-50 flex items-center gap-2"
          >
            {isLoggingOut ? (
              <>
                <svg className="animate-spin h-4 w-4" viewBox="0 0 24 24">
                  <circle className="opacity-25" cx="12" cy="12" r="10" stroke="currentColor" strokeWidth="4" fill="none" />
                  <path className="opacity-75" fill="currentColor" d="M4 12a8 8 0 018-8V0C5.373 0 0 5.373 0 12h4zm2 5.291A7.962 7.962 0 014 12H0c0 3.042 1.135 5.824 3 7.938l3-2.647z" />
                </svg>
                Clearing...
              </>
            ) : (
              <>
                <svg className="w-4 h-4" fill="none" stroke="currentColor" viewBox="0 0 24 24">
                  <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M4 4v5h.582m15.356 2A8.001 8.001 0 004.582 9m0 0H9m11 11v-5h-.581m0 0a8.003 8.003 0 01-15.357-2m15.357 2H15" />
                </svg>
                Clear Tokens & Re-authenticate
              </>
            )}
          </button>
        </footer>
      </div>
    </div>
  );
};

export default ReauthModal;
