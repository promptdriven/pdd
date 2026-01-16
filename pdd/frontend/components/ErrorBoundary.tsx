import React, { ErrorInfo, ReactNode } from 'react';

interface ErrorBoundaryProps {
  children: ReactNode;
  fallback?: ReactNode;
}

interface ErrorBoundaryState {
  hasError: boolean;
  error: Error | null;
  errorInfo: ErrorInfo | null;
}

// Use declare to tell TypeScript this extends React.Component
declare class ReactComponent<P, S> extends React.Component<P, S> {
  state: S;
  props: P;
  setState(state: Partial<S>): void;
}

class ErrorBoundary extends (React.Component as typeof ReactComponent)<ErrorBoundaryProps, ErrorBoundaryState> {
  state: ErrorBoundaryState = { hasError: false, error: null, errorInfo: null };

  static getDerivedStateFromError(error: Error): Partial<ErrorBoundaryState> {
    return { hasError: true, error, errorInfo: null };
  }

  componentDidCatch(error: Error, errorInfo: ErrorInfo): void {
    console.error('ErrorBoundary caught an error:', error, errorInfo);
    this.setState({ error, errorInfo });
  }

  render(): ReactNode {
    if (this.state.hasError) {
      if (this.props.fallback) {
        return this.props.fallback;
      }

      return (
        <div className="min-h-screen bg-surface-950 flex items-center justify-center p-4">
          <div className="bg-red-900/20 border border-red-500/50 rounded-xl p-6 max-w-2xl w-full">
            <h1 className="text-xl font-bold text-red-400 mb-4">Something went wrong</h1>
            <div className="bg-surface-900 rounded-lg p-4 mb-4 overflow-auto max-h-64">
              <pre className="text-sm text-red-300 whitespace-pre-wrap">
                {this.state.error?.toString()}
              </pre>
              {this.state.errorInfo && (
                <pre className="text-xs text-surface-400 mt-2 whitespace-pre-wrap">
                  {this.state.errorInfo.componentStack}
                </pre>
              )}
            </div>
            <button
              onClick={() => {
                // Clear localStorage that might be causing issues
                localStorage.removeItem('pdd-task-queue');
                window.location.reload();
              }}
              className="px-4 py-2 bg-red-600 text-white rounded-lg hover:bg-red-500 transition-colors"
            >
              Clear Queue Data & Reload
            </button>
          </div>
        </div>
      );
    }

    return this.props.children;
  }
}

export default ErrorBoundary;
