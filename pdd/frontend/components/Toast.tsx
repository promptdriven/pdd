/**
 * Toast - Notification toast component for job completion alerts.
 *
 * Features:
 * - Multiple toast support
 * - Auto-dismiss with configurable duration
 * - Success/error/info variants
 * - Browser notification support
 */

import React, { useState, useEffect, useCallback, createContext, useContext } from 'react';

export type ToastType = 'success' | 'error' | 'info';

export interface ToastMessage {
  id: string;
  message: string;
  type: ToastType;
  duration?: number;
}

interface ToastContextType {
  addToast: (message: string, type: ToastType, duration?: number) => void;
  removeToast: (id: string) => void;
}

const ToastContext = createContext<ToastContextType | null>(null);

/**
 * Request browser notification permission.
 */
async function requestNotificationPermission(): Promise<boolean> {
  if (!('Notification' in window)) {
    return false;
  }
  if (Notification.permission === 'granted') {
    return true;
  }
  if (Notification.permission !== 'denied') {
    const permission = await Notification.requestPermission();
    return permission === 'granted';
  }
  return false;
}

/**
 * Show browser notification (if permitted).
 */
function showBrowserNotification(title: string, body: string, icon?: string) {
  if (Notification.permission === 'granted') {
    new Notification(title, {
      body,
      icon: icon || '/favicon.ico',
      silent: false,
    });
  }
}

/**
 * Individual toast component.
 */
const ToastItem: React.FC<{
  toast: ToastMessage;
  onDismiss: () => void;
}> = ({ toast, onDismiss }) => {
  useEffect(() => {
    if (toast.duration && toast.duration > 0) {
      const timer = setTimeout(onDismiss, toast.duration);
      return () => clearTimeout(timer);
    }
  }, [toast.duration, onDismiss]);

  const styles = {
    success: {
      bg: 'bg-green-500/20',
      border: 'border-green-500/30',
      text: 'text-green-400',
      icon: (
        <svg className="w-5 h-5" fill="none" stroke="currentColor" viewBox="0 0 24 24">
          <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M5 13l4 4L19 7" />
        </svg>
      ),
    },
    error: {
      bg: 'bg-red-500/20',
      border: 'border-red-500/30',
      text: 'text-red-400',
      icon: (
        <svg className="w-5 h-5" fill="none" stroke="currentColor" viewBox="0 0 24 24">
          <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M6 18L18 6M6 6l12 12" />
        </svg>
      ),
    },
    info: {
      bg: 'bg-accent-500/20',
      border: 'border-accent-500/30',
      text: 'text-accent-400',
      icon: (
        <svg className="w-5 h-5" fill="none" stroke="currentColor" viewBox="0 0 24 24">
          <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M13 16h-1v-4h-1m1-4h.01M21 12a9 9 0 11-18 0 9 9 0 0118 0z" />
        </svg>
      ),
    },
  };

  const style = styles[toast.type];

  return (
    <div
      className={`
        flex items-center gap-3 px-4 py-3 rounded-xl border backdrop-blur-lg shadow-lg
        ${style.bg} ${style.border}
      `}
      style={{
        animation: 'slideIn 0.3s ease-out',
      }}
    >
      <span className={style.text}>{style.icon}</span>
      <p className="text-sm text-white flex-1">{toast.message}</p>
      <button
        onClick={onDismiss}
        className="text-surface-400 hover:text-white transition-colors"
      >
        <svg className="w-4 h-4" fill="none" stroke="currentColor" viewBox="0 0 24 24">
          <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M6 18L18 6M6 6l12 12" />
        </svg>
      </button>
    </div>
  );
};

/**
 * Global styles for toast animations.
 */
const ToastStyles: React.FC = () => (
  <style>{`
    @keyframes slideIn {
      from {
        transform: translateX(100%);
        opacity: 0;
      }
      to {
        transform: translateX(0);
        opacity: 1;
      }
    }
    @keyframes indeterminate {
      0% {
        transform: translateX(-100%);
      }
      100% {
        transform: translateX(400%);
      }
    }
    .animate-indeterminate {
      animation: indeterminate 1.5s ease-in-out infinite;
    }
  `}</style>
);

/**
 * Toast container that renders all active toasts.
 */
const ToastContainer: React.FC<{
  toasts: ToastMessage[];
  removeToast: (id: string) => void;
}> = ({ toasts, removeToast }) => {
  return (
    <>
      <ToastStyles />
      {toasts.length > 0 && (
        <div className="fixed top-4 right-4 z-[100] space-y-2 max-w-sm">
          {toasts.map((toast) => (
            <ToastItem
              key={toast.id}
              toast={toast}
              onDismiss={() => removeToast(toast.id)}
            />
          ))}
        </div>
      )}
    </>
  );
};

/**
 * Toast provider component.
 */
export const ToastProvider: React.FC<{ children: React.ReactNode }> = ({ children }) => {
  const [toasts, setToasts] = useState<ToastMessage[]>([]);

  const removeToast = useCallback((id: string) => {
    setToasts((prev) => prev.filter((t) => t.id !== id));
  }, []);

  const addToast = useCallback((message: string, type: ToastType, duration: number = 5000) => {
    const id = `${Date.now()}-${Math.random().toString(36).substr(2, 9)}`;
    const toast: ToastMessage = { id, message, type, duration };

    setToasts((prev) => [...prev, toast]);

    // Also show browser notification for job completions when tab is not focused
    if (document.hidden && (type === 'success' || type === 'error')) {
      showBrowserNotification(
        type === 'success' ? 'Job Completed' : 'Job Failed',
        message
      );
    }
  }, []);

  // Request notification permission on mount
  useEffect(() => {
    requestNotificationPermission();
  }, []);

  return (
    <ToastContext.Provider value={{ addToast, removeToast }}>
      {children}
      <ToastContainer toasts={toasts} removeToast={removeToast} />
    </ToastContext.Provider>
  );
};

/**
 * Hook to use toast notifications.
 */
export function useToast() {
  const context = useContext(ToastContext);
  if (!context) {
    throw new Error('useToast must be used within a ToastProvider');
  }
  return context;
}

export default ToastProvider;
