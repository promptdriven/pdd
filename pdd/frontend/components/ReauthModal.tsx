import React, { useState, useEffect, useCallback, useRef } from 'react';
import { api, AuthStatus, LoginResponse, LoginPollResponse } from '../api';

interface ReauthModalProps {
  onClose: () => void;
}

type LoginState =
  | { phase: 'idle' }
  | { phase: 'starting' }
  | { phase: 'waiting'; userCode: string; verificationUri: string; pollId: string; expiresAt: number }
  | { phase: 'success' }
  | { phase: 'error'; message: string };

const ReauthModal: React.FC<ReauthModalProps> = ({ onClose }) => {
  const [authStatus, setAuthStatus] = useState<AuthStatus | null>(null);
  const [loginState, setLoginState] = useState<LoginState>({ phase: 'idle' });
  const [copied, setCopied] = useState(false);
  const [noBrowser, setNoBrowser] = useState(false);
  const pollIntervalRef = useRef<number | null>(null);

  // Fetch initial auth status
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

  // Cleanup polling on unmount
  useEffect(() => {
    return () => {
      if (pollIntervalRef.current) {
        clearInterval(pollIntervalRef.current);
      }
    };
  }, []);

  // Start polling for login completion
  const startPolling = useCallback((pollId: string) => {
    if (pollIntervalRef.current) {
      clearInterval(pollIntervalRef.current);
    }

    const poll = async () => {
      try {
        const result: LoginPollResponse = await api.pollLoginStatus(pollId);

        if (result.status === 'completed') {
          if (pollIntervalRef.current) {
            clearInterval(pollIntervalRef.current);
            pollIntervalRef.current = null;
          }
          setLoginState({ phase: 'success' });
          // Update auth status
          const newStatus = await api.getAuthStatus();
          setAuthStatus(newStatus);
        } else if (result.status === 'expired') {
          if (pollIntervalRef.current) {
            clearInterval(pollIntervalRef.current);
            pollIntervalRef.current = null;
          }
          setLoginState({ phase: 'error', message: result.message || 'Authentication timed out. Please try again.' });
        } else if (result.status === 'error') {
          if (pollIntervalRef.current) {
            clearInterval(pollIntervalRef.current);
            pollIntervalRef.current = null;
          }
          setLoginState({ phase: 'error', message: result.message || 'Authentication failed.' });
        }
        // 'pending' status - keep polling
      } catch (e) {
        // Network error - keep polling, don't fail immediately
        console.error('Poll error:', e);
      }
    };

    // Poll immediately, then every 3 seconds
    poll();
    pollIntervalRef.current = window.setInterval(poll, 3000);
  }, []);

  const handleLogin = async () => {
    setLoginState({ phase: 'starting' });
    setCopied(false);

    try {
      // Pass the user's browser preference
      const response: LoginResponse = await api.startLogin({ no_browser: noBrowser });

      if (!response.success || !response.user_code || !response.verification_uri || !response.poll_id) {
        setLoginState({
          phase: 'error',
          message: response.error || 'Failed to start authentication'
        });
        return;
      }

      const expiresAt = Date.now() + (response.expires_in || 900) * 1000;
      setLoginState({
        phase: 'waiting',
        userCode: response.user_code,
        verificationUri: response.verification_uri,
        pollId: response.poll_id,
        expiresAt,
      });

      // Start polling for completion
      startPolling(response.poll_id);
    } catch (e) {
      setLoginState({
        phase: 'error',
        message: e instanceof Error ? e.message : 'Failed to start authentication'
      });
    }
  };

  const handleCopyCode = async () => {
    if (loginState.phase === 'waiting') {
      try {
        await navigator.clipboard.writeText(loginState.userCode);
        setCopied(true);
        setTimeout(() => setCopied(false), 2000);
      } catch (e) {
        console.error('Failed to copy:', e);
      }
    }
  };

  const handleTryAgain = () => {
    if (pollIntervalRef.current) {
      clearInterval(pollIntervalRef.current);
      pollIntervalRef.current = null;
    }
    setLoginState({ phase: 'idle' });
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
        className="bg-gray-800 rounded-none sm:rounded-lg shadow-xl w-full h-full sm:h-auto sm:max-w-md sm:max-h-[90vh] flex flex-col ring-1 ring-white/10 overflow-y-auto"
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

          {/* Login Flow States */}
          {loginState.phase === 'idle' && (
            <div className="space-y-3">
              <p className="text-sm text-gray-300">
                Click the button below to authenticate with GitHub.
                {!noBrowser && ' A browser window will open for you to authorize PDD.'}
              </p>

              {/* Browser control checkbox */}
              <label className="flex items-center gap-2 text-sm text-gray-400 cursor-pointer hover:text-gray-300 transition-colors">
                <input
                  type="checkbox"
                  checked={noBrowser}
                  onChange={(e) => setNoBrowser(e.target.checked)}
                  className="w-4 h-4 rounded border-gray-600 bg-gray-700 text-blue-500 focus:ring-2 focus:ring-blue-500 focus:ring-offset-0 cursor-pointer"
                />
                <span>Don't open browser automatically (I'll open the link manually)</span>
              </label>
            </div>
          )}

          {loginState.phase === 'starting' && (
            <div className="flex items-center justify-center gap-3 py-6">
              <svg className="animate-spin h-6 w-6 text-blue-400" viewBox="0 0 24 24">
                <circle className="opacity-25" cx="12" cy="12" r="10" stroke="currentColor" strokeWidth="4" fill="none" />
                <path className="opacity-75" fill="currentColor" d="M4 12a8 8 0 018-8V0C5.373 0 0 5.373 0 12h4zm2 5.291A7.962 7.962 0 014 12H0c0 3.042 1.135 5.824 3 7.938l3-2.647z" />
              </svg>
              <span className="text-gray-300">Starting GitHub authentication...</span>
            </div>
          )}

          {loginState.phase === 'waiting' && (
            <div className="space-y-4">
              <div className="text-center space-y-2">
                <p className="text-sm text-gray-300">
                  {noBrowser
                    ? 'Open the link below in your browser and enter this code on GitHub:'
                    : 'A browser window has opened. Enter this code on GitHub:'}
                </p>
                <button
                  onClick={handleCopyCode}
                  className="group relative inline-flex items-center gap-2 px-6 py-3 bg-gray-700 rounded-lg hover:bg-gray-600 transition-colors"
                  title="Click to copy"
                >
                  <span
                    className="text-2xl font-mono font-bold text-white tracking-wider"
                    aria-label="Device verification code"
                  >
                    {loginState.userCode}
                  </span>
                  <svg className="w-5 h-5 text-gray-400 group-hover:text-white transition-colors" fill="none" stroke="currentColor" viewBox="0 0 24 24">
                    <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M8 16H6a2 2 0 01-2-2V6a2 2 0 012-2h8a2 2 0 012 2v2m-6 12h8a2 2 0 002-2v-8a2 2 0 00-2-2h-8a2 2 0 00-2 2v8a2 2 0 002 2z" />
                  </svg>
                  {copied && (
                    <span className="absolute -top-8 left-1/2 -translate-x-1/2 px-2 py-1 bg-green-600 text-white text-xs rounded">
                      Copied!
                    </span>
                  )}
                </button>
              </div>

              <div className="flex items-center justify-center gap-2 text-sm text-gray-400">
                <svg className="animate-spin h-4 w-4" viewBox="0 0 24 24">
                  <circle className="opacity-25" cx="12" cy="12" r="10" stroke="currentColor" strokeWidth="4" fill="none" />
                  <path className="opacity-75" fill="currentColor" d="M4 12a8 8 0 018-8V0C5.373 0 0 5.373 0 12h4zm2 5.291A7.962 7.962 0 014 12H0c0 3.042 1.135 5.824 3 7.938l3-2.647z" />
                </svg>
                <span>Waiting for authorization...</span>
              </div>

              <p className="text-xs text-center text-gray-500">
                {noBrowser ? 'Visit: ' : 'If the browser didn\'t open, go to: '}
                <a
                  href={loginState.verificationUri}
                  target="_blank"
                  rel="noopener noreferrer"
                  className="text-blue-400 hover:underline"
                >
                  {loginState.verificationUri}
                </a>
              </p>
            </div>
          )}

          {loginState.phase === 'success' && (
            <div className="p-4 rounded-lg bg-green-500/20 border border-green-500/30 text-center space-y-2">
              <svg className="w-12 h-12 mx-auto text-green-400" fill="none" stroke="currentColor" viewBox="0 0 24 24">
                <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M9 12l2 2 4-4m6 2a9 9 0 11-18 0 9 9 0 0118 0z" />
              </svg>
              <p className="text-green-300 font-medium">Authentication Successful!</p>
              <p className="text-sm text-green-400/80">You can now use PDD Cloud features.</p>
            </div>
          )}

          {loginState.phase === 'error' && (
            <div className="p-4 rounded-lg bg-red-500/20 border border-red-500/30 space-y-3">
              <div className="flex items-start gap-3">
                <svg className="w-5 h-5 text-red-400 flex-shrink-0 mt-0.5" fill="none" stroke="currentColor" viewBox="0 0 24 24">
                  <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M12 8v4m0 4h.01M21 12a9 9 0 11-18 0 9 9 0 0118 0z" />
                </svg>
                <p className="text-sm text-red-300">{loginState.message}</p>
              </div>
              <button
                onClick={handleTryAgain}
                className="w-full px-3 py-2 text-sm bg-red-600/30 hover:bg-red-600/50 text-red-200 rounded transition-colors"
              >
                Try Again
              </button>
            </div>
          )}
        </main>

        <footer className="px-6 py-4 bg-gray-800/50 border-t border-gray-700 flex justify-end gap-3 rounded-b-lg">
          <button
            type="button"
            onClick={onClose}
            className="px-4 py-2 rounded-md text-sm font-medium bg-gray-600 text-white hover:bg-gray-700 focus:outline-none focus:ring-2 focus:ring-offset-2 focus:ring-offset-gray-800 focus:ring-gray-500 transition-colors"
          >
            {loginState.phase === 'success' ? 'Done' : 'Close'}
          </button>
          {(loginState.phase === 'idle' || loginState.phase === 'error') && (
            <button
              onClick={handleLogin}
              className="px-4 py-2 rounded-md text-sm font-medium bg-blue-600 text-white hover:bg-blue-700 focus:outline-none focus:ring-2 focus:ring-offset-2 focus:ring-offset-gray-800 focus:ring-blue-500 transition-colors flex items-center gap-2"
            >
              {/* GitHub icon */}
              <svg className="w-5 h-5" fill="currentColor" viewBox="0 0 24 24">
                <path fillRule="evenodd" clipRule="evenodd" d="M12 2C6.477 2 2 6.477 2 12c0 4.42 2.865 8.17 6.839 9.49.5.092.682-.217.682-.482 0-.237-.008-.866-.013-1.7-2.782.603-3.369-1.342-3.369-1.342-.454-1.155-1.11-1.462-1.11-1.462-.908-.62.069-.608.069-.608 1.003.07 1.531 1.03 1.531 1.03.892 1.529 2.341 1.087 2.91.832.092-.647.35-1.088.636-1.338-2.22-.253-4.555-1.11-4.555-4.943 0-1.091.39-1.984 1.029-2.683-.103-.253-.446-1.27.098-2.647 0 0 .84-.269 2.75 1.025A9.578 9.578 0 0112 6.836c.85.004 1.705.114 2.504.336 1.909-1.294 2.747-1.025 2.747-1.025.546 1.377.203 2.394.1 2.647.64.699 1.028 1.592 1.028 2.683 0 3.842-2.339 4.687-4.566 4.935.359.309.678.919.678 1.852 0 1.336-.012 2.415-.012 2.743 0 .267.18.578.688.48C19.138 20.167 22 16.418 22 12c0-5.523-4.477-10-10-10z" />
              </svg>
              Login with GitHub
            </button>
          )}
        </footer>
      </div>
    </div>
  );
};

export default ReauthModal;
