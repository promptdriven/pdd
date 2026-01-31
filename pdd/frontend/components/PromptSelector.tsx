import React, { useState, useEffect, useMemo } from 'react';
import { api, PromptInfo } from '../api';
import CreatePromptModal from './CreatePromptModal';
import SyncOptionsModal from './SyncOptionsModal';

interface PromptSelectorProps {
  onEditPrompt: (prompt: PromptInfo) => void;
  onCreatePrompt?: (prompt: PromptInfo) => void;
  onRunSync?: (prompt: PromptInfo, options?: Record<string, any>) => void;
  onAddToQueue?: (prompt: PromptInfo, options?: Record<string, any>) => void;
  selectedPrompt: PromptInfo | null;
}

// Language badge colors - Modern gradient approach
const LANGUAGE_COLORS: Record<string, string> = {
  python: 'bg-blue-500/15 text-blue-300 border-blue-500/30',
  typescript: 'bg-cyan-500/15 text-cyan-300 border-cyan-500/30',
  javascript: 'bg-yellow-500/15 text-yellow-300 border-yellow-500/30',
  java: 'bg-orange-500/15 text-orange-300 border-orange-500/30',
  go: 'bg-teal-500/15 text-teal-300 border-teal-500/30',
  rust: 'bg-red-500/15 text-red-300 border-red-500/30',
};

const PromptCard: React.FC<{
  prompt: PromptInfo;
  isSelected: boolean;
  onEditPrompt: () => void;
  onSyncClick?: () => void;
}> = ({ prompt, isSelected, onEditPrompt, onSyncClick }) => {
  const languageColor = prompt.language
    ? LANGUAGE_COLORS[prompt.language] || 'bg-surface-700/50 text-surface-300 border-surface-600'
    : 'bg-surface-700/50 text-surface-300 border-surface-600';

  const handleCardClick = (e: React.MouseEvent) => {
    e.stopPropagation();
    onEditPrompt();
  };

  const handleSyncClick = (e: React.MouseEvent) => {
    e.stopPropagation();
    if (onSyncClick) {
      onSyncClick();
    }
  };

  return (
    <>
      <div
        className={`
          glass rounded-xl sm:rounded-2xl border transition-all duration-200 card-hover
          ${isSelected
            ? 'border-accent-500/50 shadow-lg shadow-accent-500/10 ring-1 ring-accent-500/20'
            : 'border-surface-700/50 hover:border-surface-600'}
        `}
      >
        {/* Card - click to open prompt space */}
        <div className="p-3 sm:p-4 cursor-pointer" onClick={handleCardClick}>
          <div className="flex items-start justify-between gap-2 mb-2 sm:mb-3">
            <div className="flex items-center gap-2 flex-wrap min-w-0">
              <h3 className="text-base sm:text-lg font-semibold text-white truncate">{prompt.sync_basename}</h3>
              {prompt.language && (
                <span className={`px-2 py-0.5 rounded-full text-[10px] sm:text-xs border font-medium ${languageColor}`}>
                  {prompt.language}
                </span>
              )}
            </div>
            {/* Sync button */}
            {onSyncClick && (
              <button
                onClick={handleSyncClick}
                className="flex-shrink-0 w-7 h-7 bg-gradient-to-br from-[#FDCE49] to-[#DFA84A] hover:from-[#FFD966] hover:to-[#FDCE49] rounded-full flex items-center justify-center shadow-lg transition-all hover:scale-110"
                title="Run pdd sync (prompt → code)"
              >
                <svg className="w-3.5 h-3.5 text-surface-900" fill="none" stroke="currentColor" viewBox="0 0 24 24">
                  <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2.5} d="M4 4v5h.582m15.356 2A8.001 8.001 0 004.582 9m0 0H9m11 11v-5h-.581m0 0a8.003 8.003 0 01-15.357-2m15.357 2H15" />
                </svg>
              </button>
            )}
          </div>
          <p className="text-[10px] sm:text-xs text-surface-400 font-mono mb-2 sm:mb-3 truncate">{prompt.prompt}</p>

          {/* Related files - responsive grid */}
          <div className="flex gap-1.5 sm:gap-2 flex-wrap">
            <FileTag label="Prompt" path={prompt.prompt} exists={true} color="purple" />
            <FileTag label="Code" path={prompt.code} exists={!!prompt.code} color="green" />
            <FileTag label="Test" path={prompt.test} exists={!!prompt.test} color="yellow" />
            <FileTag label="Example" path={prompt.example} exists={!!prompt.example} color="blue" />
          </div>
        </div>

      </div>
    </>
  );
};

const FileTag: React.FC<{
  label: string;
  path?: string;
  exists: boolean;
  color: 'purple' | 'green' | 'yellow' | 'blue';
}> = ({ label, path, exists, color }) => {
  const colorClasses = {
    purple: exists ? 'bg-purple-500/15 text-purple-300 border-purple-500/30' : 'bg-surface-800/50 text-surface-500 border-surface-700/50',
    green: exists ? 'bg-green-500/15 text-green-300 border-green-500/30' : 'bg-surface-800/50 text-surface-500 border-surface-700/50',
    yellow: exists ? 'bg-yellow-500/15 text-yellow-300 border-yellow-500/30' : 'bg-surface-800/50 text-surface-500 border-surface-700/50',
    blue: exists ? 'bg-blue-500/15 text-blue-300 border-blue-500/30' : 'bg-surface-800/50 text-surface-500 border-surface-700/50',
  };

  return (
    <span
      className={`inline-flex items-center gap-1 px-1.5 sm:px-2 py-0.5 rounded-md text-[10px] sm:text-xs border font-medium ${colorClasses[color]}`}
      title={path || `No ${label.toLowerCase()} file`}
    >
      <span className={exists ? 'text-green-400' : 'text-surface-500'}>{exists ? '✓' : '✗'}</span>
      <span>{label}</span>
    </span>
  );
};

const PromptSelector: React.FC<PromptSelectorProps> = ({
  onEditPrompt,
  onCreatePrompt,
  onRunSync,
  onAddToQueue,
  selectedPrompt,
}) => {
  const [prompts, setPrompts] = useState<PromptInfo[]>([]);
  const [loading, setLoading] = useState(true);
  const [error, setError] = useState<string | null>(null);
  const [searchQuery, setSearchQuery] = useState('');
  const [showCreateModal, setShowCreateModal] = useState(false);
  const [isCreating, setIsCreating] = useState(false);
  const [showChangedOnly, setShowChangedOnly] = useState(false);
  const [changedPrompts, setChangedPrompts] = useState<string[]>([]);
  const [loadingChanged, setLoadingChanged] = useState(false);

  // Sync options modal state
  const [showSyncOptionsModal, setShowSyncOptionsModal] = useState(false);
  const [pendingSyncPrompt, setPendingSyncPrompt] = useState<PromptInfo | null>(null);

  // Filter prompts based on search query and changed-only filter
  const filteredPrompts = useMemo(() => {
    let filtered = prompts;

    // Apply changed-only filter
    if (showChangedOnly && changedPrompts.length > 0) {
      filtered = filtered.filter(p => changedPrompts.includes(p.prompt));
    }

    // Apply search filter
    if (searchQuery.trim()) {
      const query = searchQuery.toLowerCase();
      filtered = filtered.filter(p =>
        p.sync_basename.toLowerCase().includes(query) ||
        p.prompt.toLowerCase().includes(query) ||
        (p.language && p.language.toLowerCase().includes(query))
      );
    }

    return filtered;
  }, [prompts, searchQuery, showChangedOnly, changedPrompts]);

  useEffect(() => {
    loadPrompts();
    loadChangedPrompts();
  }, []);

  const loadChangedPrompts = async () => {
    setLoadingChanged(true);
    try {
      const data = await api.getChangedPrompts();
      setChangedPrompts(data.changed_prompts);
    } catch (e: any) {
      // Silently fail - this is an optional feature
      console.warn('Failed to load changed prompts:', e.message);
      setChangedPrompts([]);
    } finally {
      setLoadingChanged(false);
    }
  };

  const loadPrompts = async () => {
    setLoading(true);
    setError(null);
    try {
      const data = await api.listPrompts();
      setPrompts(data);
    } catch (e: any) {
      setError(e.message || 'Failed to load prompts');
    } finally {
      setLoading(false);
    }
  };

  // Handle creating a new prompt
  const handleCreatePrompt = async (promptData: { path: string; content: string; info: PromptInfo }) => {
    setIsCreating(true);
    try {
      await api.writeFile(promptData.path, promptData.content);
      await loadPrompts();
      setShowCreateModal(false);
      // Navigate to PromptSpace to edit the new prompt
      if (onCreatePrompt) {
        onCreatePrompt(promptData.info);
      }
    } catch (e: any) {
      throw new Error(e.message || 'Failed to create prompt');
    } finally {
      setIsCreating(false);
    }
  };

  if (loading) {
    return (
      <div className="flex flex-col items-center justify-center py-16 sm:py-20">
        <div className="w-10 h-10 rounded-xl bg-accent-500/20 flex items-center justify-center mb-4">
          <svg className="animate-spin h-5 w-5 text-accent-400" viewBox="0 0 24 24">
            <circle className="opacity-25" cx="12" cy="12" r="10" stroke="currentColor" strokeWidth="4" fill="none" />
            <path className="opacity-75" fill="currentColor" d="M4 12a8 8 0 018-8V0C5.373 0 0 5.373 0 12h4z" />
          </svg>
        </div>
        <div className="text-surface-400 text-sm">Loading prompts...</div>
      </div>
    );
  }

  if (error) {
    return (
      <div className="flex flex-col items-center justify-center py-16 sm:py-20">
        <div className="w-12 h-12 rounded-xl bg-red-500/20 flex items-center justify-center mb-4">
          <svg className="w-6 h-6 text-red-400" fill="none" stroke="currentColor" viewBox="0 0 24 24">
            <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M12 9v2m0 4h.01m-6.938 4h13.856c1.54 0 2.502-1.667 1.732-3L13.732 4c-.77-1.333-2.694-1.333-3.464 0L3.34 16c-.77 1.333.192 3 1.732 3z" />
          </svg>
        </div>
        <div className="text-red-400 mb-2 text-center">{error}</div>
        <button
          onClick={loadPrompts}
          className="px-4 py-2 bg-surface-700/50 hover:bg-surface-600 rounded-xl text-sm text-white transition-colors border border-surface-600"
        >
          Try Again
        </button>
      </div>
    );
  }

  if (prompts.length === 0) {
    return (
      <div className="flex flex-col items-center justify-center py-16 sm:py-20">
        <div className="w-14 h-14 rounded-2xl bg-surface-700/50 flex items-center justify-center mb-5">
          <svg className="w-7 h-7 text-surface-400" fill="none" stroke="currentColor" viewBox="0 0 24 24">
            <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M9 12h6m-6 4h6m2 5H7a2 2 0 01-2-2V5a2 2 0 012-2h5.586a1 1 0 01.707.293l5.414 5.414a1 1 0 01.293.707V19a2 2 0 01-2 2z" />
          </svg>
        </div>
        <div className="text-surface-200 mb-2 font-semibold text-lg">No prompts found</div>
        <p className="text-surface-500 text-sm text-center mb-6 max-w-sm">
          Get started by creating your first prompt, or add <code className="bg-surface-800/80 px-1.5 py-0.5 rounded text-accent-300">.prompt</code> files to the <code className="bg-surface-800/80 px-1.5 py-0.5 rounded text-accent-300">prompts/</code> directory.
        </p>
        <button
          onClick={() => setShowCreateModal(true)}
          className="flex items-center gap-2 px-5 py-2.5 bg-gradient-to-r from-accent-600 to-accent-500 hover:from-accent-500 hover:to-accent-400 text-white rounded-xl font-medium shadow-lg shadow-accent-500/25 transition-all"
        >
          <svg className="w-4 h-4" fill="none" stroke="currentColor" viewBox="0 0 24 24">
            <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M12 4v16m8-8H4" />
          </svg>
          Create Your First Prompt
        </button>

        {showCreateModal && (
          <CreatePromptModal
            onClose={() => setShowCreateModal(false)}
            onCreate={handleCreatePrompt}
            isCreating={isCreating}
            existingPrompts={prompts}
          />
        )}
      </div>
    );
  }

  return (
    <div className="space-y-3 sm:space-y-4">
      {/* Header with title and refresh */}
      <div className="flex items-center justify-between">
        <h2 className="text-base sm:text-lg font-semibold text-white flex items-center gap-2">
          <span className="hidden sm:inline">Your Prompts</span>
          <span className="sm:hidden">Prompts</span>
          <span className="px-2 py-0.5 rounded-full bg-accent-500/20 text-accent-300 text-xs font-medium">
            {filteredPrompts.length}{(searchQuery || showChangedOnly) ? `/${prompts.length}` : ''}
          </span>
        </h2>
        <div className="flex items-center gap-2">
          {/* Changed Only Filter Toggle */}
          <button
            onClick={() => setShowChangedOnly(!showChangedOnly)}
            disabled={loadingChanged}
            className={`flex items-center gap-1.5 px-2.5 sm:px-3 py-1.5 text-xs sm:text-sm rounded-lg transition-colors border ${
              showChangedOnly
                ? 'bg-green-600/20 text-green-300 border-green-500/50 hover:bg-green-600/30'
                : 'text-surface-400 hover:text-white bg-surface-800/50 hover:bg-surface-700 border-surface-700/50'
            }`}
            title={showChangedOnly ? 'Show all prompts' : 'Show only changed prompts (compared to main)'}
          >
            {loadingChanged ? (
              <svg className="animate-spin w-3.5 h-3.5" viewBox="0 0 24 24">
                <circle className="opacity-25" cx="12" cy="12" r="10" stroke="currentColor" strokeWidth="4" fill="none" />
                <path className="opacity-75" fill="currentColor" d="M4 12a8 8 0 018-8V0C5.373 0 0 5.373 0 12h4z" />
              </svg>
            ) : (
              <svg className="w-3.5 h-3.5" fill="none" stroke="currentColor" viewBox="0 0 24 24">
                <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M9 5H7a2 2 0 00-2 2v12a2 2 0 002 2h10a2 2 0 002-2V7a2 2 0 00-2-2h-2M9 5a2 2 0 002 2h2a2 2 0 002-2M9 5a2 2 0 012-2h2a2 2 0 012 2m-6 9l2 2 4-4" />
              </svg>
            )}
            <span className="hidden sm:inline">Changed</span>
            {showChangedOnly && changedPrompts.length > 0 && (
              <span className="px-1.5 py-0.5 rounded-full bg-green-500/30 text-green-200 text-[10px] font-medium">
                {changedPrompts.length}
              </span>
            )}
          </button>
          <button
            onClick={() => setShowCreateModal(true)}
            className="flex items-center gap-1.5 px-2.5 sm:px-3 py-1.5 text-xs sm:text-sm bg-accent-600 hover:bg-accent-500 text-white rounded-lg transition-colors"
            title="Create new prompt"
          >
            <svg className="w-3.5 h-3.5" fill="none" stroke="currentColor" viewBox="0 0 24 24">
              <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M12 4v16m8-8H4" />
            </svg>
            <span className="hidden sm:inline">New</span>
          </button>
          <button
            onClick={() => { loadPrompts(); loadChangedPrompts(); }}
            className="flex items-center gap-1.5 px-2.5 sm:px-3 py-1.5 text-xs sm:text-sm text-surface-400 hover:text-white bg-surface-800/50 hover:bg-surface-700 rounded-lg transition-colors border border-surface-700/50"
            title="Refresh"
          >
            <svg className="w-3.5 h-3.5" fill="none" stroke="currentColor" viewBox="0 0 24 24">
              <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M4 4v5h.582m15.356 2A8.001 8.001 0 004.582 9m0 0H9m11 11v-5h-.581m0 0a8.003 8.003 0 01-15.357-2m15.357 2H15" />
            </svg>
            <span className="hidden sm:inline">Refresh</span>
          </button>
        </div>
      </div>

      {/* Search input - Modern design */}
      <div className="relative">
        <input
          type="text"
          placeholder="Search prompts..."
          value={searchQuery}
          onChange={(e) => setSearchQuery(e.target.value)}
          className="w-full px-3 sm:px-4 py-2.5 sm:py-3 pl-9 sm:pl-11 bg-surface-800/50 border border-surface-600/50 rounded-xl text-white placeholder-surface-500 focus:outline-none focus:border-accent-500 focus:ring-1 focus:ring-accent-500/50 text-sm sm:text-base transition-all"
        />
        <span className="absolute left-3 sm:left-4 top-1/2 -translate-y-1/2 text-surface-400">
          <svg className="w-4 h-4" fill="none" stroke="currentColor" viewBox="0 0 24 24">
            <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M21 21l-6-6m2-5a7 7 0 11-14 0 7 7 0 0114 0z" />
          </svg>
        </span>
        {searchQuery && (
          <button
            onClick={() => setSearchQuery('')}
            className="absolute right-3 top-1/2 -translate-y-1/2 text-surface-400 hover:text-white p-1 rounded-lg hover:bg-surface-700/50 transition-colors"
          >
            <svg className="w-4 h-4" fill="none" stroke="currentColor" viewBox="0 0 24 24">
              <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M6 18L18 6M6 6l12 12" />
            </svg>
          </button>
        )}
      </div>

      {filteredPrompts.length === 0 ? (
        <div className="flex flex-col items-center justify-center py-12 sm:py-16">
          <div className="w-10 h-10 rounded-xl bg-surface-700/50 flex items-center justify-center mb-3">
            <svg className="w-5 h-5 text-surface-400" fill="none" stroke="currentColor" viewBox="0 0 24 24">
              {showChangedOnly ? (
                <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M9 5H7a2 2 0 00-2 2v12a2 2 0 002 2h10a2 2 0 002-2V7a2 2 0 00-2-2h-2M9 5a2 2 0 002 2h2a2 2 0 002-2M9 5a2 2 0 012-2h2a2 2 0 012 2" />
              ) : (
                <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M21 21l-6-6m2-5a7 7 0 11-14 0 7 7 0 0114 0z" />
              )}
            </svg>
          </div>
          <div className="text-surface-400 text-sm text-center">
            {showChangedOnly && !searchQuery ? (
              <>No prompts changed on this branch</>
            ) : showChangedOnly && searchQuery ? (
              <>No changed prompts matching "<span className="text-white">{searchQuery}</span>"</>
            ) : (
              <>No prompts matching "<span className="text-white">{searchQuery}</span>"</>
            )}
          </div>
          {showChangedOnly && (
            <button
              onClick={() => setShowChangedOnly(false)}
              className="mt-3 px-3 py-1.5 text-xs text-accent-400 hover:text-accent-300 transition-colors"
            >
              Show all prompts
            </button>
          )}
        </div>
      ) : (
        <div className="grid gap-3 sm:gap-4">
          {filteredPrompts.map(prompt => (
            <PromptCard
              key={prompt.prompt}
              prompt={prompt}
              isSelected={selectedPrompt?.prompt === prompt.prompt}
              onEditPrompt={() => onEditPrompt(prompt)}
              onSyncClick={onRunSync ? () => {
                setPendingSyncPrompt(prompt);
                setShowSyncOptionsModal(true);
              } : undefined}
            />
          ))}
        </div>
      )}

      {/* Create Prompt Modal */}
      {showCreateModal && (
        <CreatePromptModal
          onClose={() => setShowCreateModal(false)}
          onCreate={handleCreatePrompt}
          isCreating={isCreating}
          existingPrompts={prompts}
        />
      )}

      {/* Sync Options Modal */}
      <SyncOptionsModal
        isOpen={showSyncOptionsModal}
        title="Sync Options"
        description={`Configure options for syncing ${pendingSyncPrompt?.sync_basename || 'prompt'}`}
        onConfirm={(options) => {
          if (pendingSyncPrompt && onRunSync) {
            onRunSync(pendingSyncPrompt, options);
          }
          setShowSyncOptionsModal(false);
          setPendingSyncPrompt(null);
        }}
        onAddToQueue={onAddToQueue ? (options) => {
          if (pendingSyncPrompt) {
            onAddToQueue(pendingSyncPrompt, options);
          }
          setShowSyncOptionsModal(false);
          setPendingSyncPrompt(null);
        } : undefined}
        onClose={() => {
          setShowSyncOptionsModal(false);
          setPendingSyncPrompt(null);
        }}
      />
    </div>
  );
};

export default PromptSelector;
