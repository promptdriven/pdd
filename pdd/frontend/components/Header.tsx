
import React from 'react';
import Tooltip from './Tooltip';

type View = 'builder' | 'dependencies';

interface HeaderProps {
  currentView: View;
  onViewChange: (view: View) => void;
}

const Header: React.FC<HeaderProps> = ({ currentView, onViewChange }) => {
  const navButtonClasses = (view: View) => `
    px-3 py-2 rounded-md text-sm font-medium transition-colors
    ${currentView === view
      ? 'bg-brand-cyan text-brand-navy'
      : 'text-gray-300 hover:bg-gray-700 hover:text-white'
    }
    focus:outline-none focus:ring-2 focus:ring-offset-2 focus:ring-offset-gray-900 focus:ring-brand-cyan
  `;

  return (
    <header className="bg-gray-900/80 backdrop-blur-sm sticky top-0 z-10 py-4 mb-8">
      <div className="max-w-7xl mx-auto px-4 sm:px-6 lg:px-8">
        <div className="flex items-center justify-between">
          <a
            href="https://promptdriven.ai"
            target="_blank"
            rel="noopener noreferrer"
            className="flex items-center gap-3 flex-1 min-w-0 group"
          >
            <img
              src="/logo.svg"
              alt="PromptDriven.ai logo"
              className="h-11 w-11 flex-shrink-0"
            />
            <div className="flex items-baseline gap-2.5 min-w-0">
              <h1 className="font-sans font-semibold tracking-[0.01em] text-brand-sleet text-3xl sm:text-4xl group-hover:text-white transition-colors">
                PromptDriven.ai
              </h1>
              <span className="font-mono font-medium uppercase tracking-[0.12em] text-brand-cyan text-[0.65rem] sm:text-xs">
                Prompt Driven Development
              </span>
            </div>
          </a>
          <nav className="flex items-center space-x-2 flex-shrink-0">
            <Tooltip content="View prompt dependency graph">
              <button onClick={() => onViewChange('dependencies')} className={navButtonClasses('dependencies')}>
                Graph
              </button>
            </Tooltip>
            <Tooltip content="Construct a pdd command">
              <button onClick={() => onViewChange('builder')} className={navButtonClasses('builder')}>
                Builder
              </button>
            </Tooltip>
          </nav>
        </div>
      </div>
    </header>
  );
};

export default Header;