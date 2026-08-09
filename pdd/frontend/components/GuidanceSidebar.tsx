import React, { useState } from 'react';
import { PDD_DIRECTIVES, BEST_PRACTICES, CATEGORY_LABELS, PDDDirective } from '../lib/pddDirectives';
import { SparklesIcon } from './Icon';

interface GuidanceSidebarProps {
  isOpen: boolean;
  onClose: () => void;
}

// Group directives by category
const groupedDirectives = PDD_DIRECTIVES.reduce((acc, directive) => {
  if (!acc[directive.category]) {
    acc[directive.category] = [];
  }
  acc[directive.category].push(directive);
  return acc;
}, {} as Record<PDDDirective['category'], PDDDirective[]>);

// Category order for display
const categoryOrder: PDDDirective['category'][] = ['include', 'dynamic', 'grounding', 'meta'];

const DirectiveCard: React.FC<{ directive: PDDDirective }> = ({ directive }) => {
  const [expanded, setExpanded] = useState(false);

  return (
    <div
      className={`rounded-md border border-surface-700/50 bg-surface-800/50 overflow-hidden transition-all duration-200 ${
        expanded ? 'ring-1 ring-accent-500/30' : ''
      }`}
    >
      <button
        onClick={() => setExpanded(!expanded)}
        className="w-full flex items-center justify-between px-3 py-2 text-left hover:bg-surface-700/30 transition-colors"
      >
        <code className="text-accent-400 font-mono text-sm">&lt;{directive.tag}&gt;</code>
        <svg
          className={`w-4 h-4 text-text-secondary transition-transform duration-200 ${
            expanded ? 'rotate-180' : ''
          }`}
          fill="none"
          viewBox="0 0 24 24"
          stroke="currentColor"
        >
          <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M19 9l-7 7-7-7" />
        </svg>
      </button>
      {expanded && (
        <div className="px-3 pb-3 pt-1 border-t border-surface-700/50 bg-surface-900/30">
          <p className="text-text-secondary text-xs mb-2">{directive.description}</p>
          <div className="bg-surface-900 rounded px-2 py-1.5">
            <code className="text-xs text-text-muted font-mono break-all">{directive.syntax}</code>
          </div>
          {directive.example && (
            <div className="mt-2">
              <span className="text-xs text-text-muted">Example:</span>
              <div className="bg-surface-900 rounded px-2 py-1.5 mt-1">
                <code className="text-xs text-accent-300 font-mono break-all">{directive.example}</code>
              </div>
            </div>
          )}
        </div>
      )}
    </div>
  );
};

const GuidanceSidebar: React.FC<GuidanceSidebarProps> = ({ isOpen, onClose }) => {
  if (!isOpen) return null;

  return (
    <aside className="w-72 flex-shrink-0 border-l border-surface-700 bg-surface-800 flex flex-col overflow-hidden animate-slide-in-right">
      {/* Header */}
      <header className="flex items-center justify-between px-4 py-3 border-b border-surface-700 bg-surface-800/80">
        <h3 className="font-semibold text-text-primary flex items-center gap-2">
          <svg className="w-4 h-4 text-accent-400" fill="none" viewBox="0 0 24 24" stroke="currentColor">
            <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M13 16h-1v-4h-1m1-4h.01M21 12a9 9 0 11-18 0 9 9 0 0118 0z" />
          </svg>
          Prompting Guide
        </h3>
        <button
          onClick={onClose}
          className="p-1 rounded hover:bg-surface-700 text-text-secondary hover:text-text-primary transition-colors"
          aria-label="Close guide"
        >
          <svg className="w-5 h-5" fill="none" viewBox="0 0 24 24" stroke="currentColor">
            <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M6 18L18 6M6 6l12 12" />
          </svg>
        </button>
      </header>

      {/* Scrollable content */}
      <div className="flex-1 overflow-y-auto">
        {/* Directives Section */}
        <section className="p-4">
          <h4 className="text-xs font-semibold text-text-muted uppercase tracking-wider mb-3">
            PDD Directives
          </h4>
          <p className="text-xs text-text-secondary mb-3">
            Type <code className="text-accent-400 bg-surface-900 px-1 rounded">&lt;</code> in the editor to trigger autocomplete.
          </p>
          <div className="space-y-4">
            {categoryOrder.map(category => {
              const directives = groupedDirectives[category];
              if (!directives || directives.length === 0) return null;
              return (
                <div key={category}>
                  <h5 className="text-xs font-medium text-text-secondary mb-2 flex items-center gap-1.5">
                    <span className={`w-2 h-2 rounded-full ${
                      category === 'include' ? 'bg-blue-400' :
                      category === 'dynamic' ? 'bg-amber-400' :
                      category === 'grounding' ? 'bg-purple-400' :
                      'bg-gray-400'
                    }`} />
                    {CATEGORY_LABELS[category]}
                  </h5>
                  <div className="space-y-1.5">
                    {directives.map(d => (
                      <DirectiveCard key={d.tag} directive={d} />
                    ))}
                  </div>
                </div>
              );
            })}
          </div>
        </section>

        {/* Divider */}
        <div className="border-t border-surface-700 mx-4" />

        {/* Best Practices Section */}
        <section className="p-4">
          <h4 className="text-xs font-semibold text-text-muted uppercase tracking-wider mb-3">
            Best Practices
          </h4>
          <div className="space-y-3">
            {BEST_PRACTICES.map((practice, index) => (
              <div key={index} className="rounded-md bg-surface-900/50 p-3">
                <h5 className="text-sm font-medium text-text-primary mb-1 flex items-center gap-2">
                  <SparklesIcon className="w-3 h-3 text-surface-400 flex-shrink-0" />
                  {practice.title}
                </h5>
                <p className="text-xs text-text-secondary leading-relaxed">{practice.content}</p>
              </div>
            ))}
          </div>
        </section>

        {/* Quick Tips */}
        <section className="p-4 pt-0">
          <div className="rounded-md bg-accent-500/10 border border-accent-500/20 p-3">
            <h5 className="text-xs font-medium text-accent-400 mb-2 flex items-center gap-1.5">
              <svg className="w-3.5 h-3.5" fill="none" viewBox="0 0 24 24" stroke="currentColor">
                <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M13 10V3L4 14h7v7l9-11h-7z" />
              </svg>
              Quick Tip
            </h5>
            <p className="text-xs text-text-secondary">
              Use <code className="text-accent-300 bg-surface-900/50 px-1 rounded">&lt;include&gt;</code> to reference a shared preamble for consistent coding style across all prompts.
            </p>
          </div>
        </section>
      </div>
    </aside>
  );
};

export default GuidanceSidebar;
