import React, { useState, useEffect } from 'react';
import { api, AuthStatus } from '../api';

interface AuthStatusIndicatorProps {
  onReauth: () => void;
}

const AuthStatusIndicator: React.FC<AuthStatusIndicatorProps> = ({ onReauth }) => {
  const [status, setStatus] = useState<AuthStatus | null>(null);
  const [loading, setLoading] = useState(true);

  useEffect(() => {
    const checkStatus = async () => {
      try {
        const s = await api.getAuthStatus();
        setStatus(s);
      } catch (e) {
        setStatus({ authenticated: false, cached: false, expires_at: null });
      } finally {
        setLoading(false);
      }
    };

    checkStatus();

    // Poll every 30 seconds
    const interval = setInterval(checkStatus, 30000);
    return () => clearInterval(interval);
  }, []);

  if (loading) {
    return (
      <div className="flex items-center gap-1.5 px-2 sm:px-3 py-1.5 rounded-full bg-surface-800/50">
        <svg className="w-3.5 h-3.5 sm:w-4 sm:h-4 text-surface-500 animate-pulse" fill="none" stroke="currentColor" viewBox="0 0 24 24">
          <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M15 7a2 2 0 012 2m4 0a6 6 0 01-7.743 5.743L11 17H9v2H7v2H4a1 1 0 01-1-1v-2.586a1 1 0 01.293-.707l5.964-5.964A6 6 0 1121 9z" />
        </svg>
        <span className="text-xs text-surface-400 hidden sm:inline">Auth...</span>
      </div>
    );
  }

  const isAuthenticated = status?.authenticated;

  return (
    <button
      onClick={onReauth}
      className={`flex items-center gap-1.5 sm:gap-2 text-xs sm:text-sm px-2 sm:px-3 py-1.5 rounded-full transition-colors ${
        isAuthenticated
          ? 'bg-blue-500/10 text-blue-400 border border-blue-500/20 hover:bg-blue-500/20'
          : 'bg-yellow-500/10 text-yellow-400 border border-yellow-500/20 hover:bg-yellow-500/20'
      }`}
      title={isAuthenticated ? 'Cloud Authenticated - Click to manage authentication' : 'Not authenticated - Click to login'}
    >
      {/* Key icon for authentication */}
      <svg className="w-3.5 h-3.5 sm:w-4 sm:h-4" fill="none" stroke="currentColor" viewBox="0 0 24 24">
        <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M15 7a2 2 0 012 2m4 0a6 6 0 01-7.743 5.743L11 17H9v2H7v2H4a1 1 0 01-1-1v-2.586a1 1 0 01.293-.707l5.964-5.964A6 6 0 1121 9z" />
      </svg>
      {/* Always show text label */}
      <span className="sr-only">
        {isAuthenticated ? 'Cloud Authenticated - Click to manage authentication' : 'Not authenticated - Click to login'}
      </span>
      <span className="hidden xs:inline" aria-hidden="true">
        {isAuthenticated ? 'Logged In' : 'Login'}
      </span>
      {/* Status dot */}
      <span className={`w-1.5 h-1.5 sm:w-2 sm:h-2 rounded-full ${
        isAuthenticated ? 'bg-blue-400' : 'bg-yellow-400 animate-pulse'
      }`} />
    </button>
  );
};

export default AuthStatusIndicator;
