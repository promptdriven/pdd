import React, { useEffect, useState, useRef } from 'react';
import { api, ModelInfo, ModelsResponse } from '../api';

interface ModelSelectorProps {
  selectedModel: ModelInfo | null;
  onModelChange: (model: ModelInfo | null) => void;
  className?: string;
}

// Format token count for display
const formatTokens = (count: number): string => {
  if (count >= 1000000) return `${(count / 1000000).toFixed(1)}M`;
  if (count >= 1000) return `${(count / 1000).toFixed(0)}K`;
  return count.toString();
};

// Format cost for display
const formatCost = (cost: number): string => {
  if (cost < 0.01) return `$${cost.toFixed(3)}`;
  return `$${cost.toFixed(2)}`;
};

// Group models by provider
const groupByProvider = (models: ModelInfo[]): Map<string, ModelInfo[]> => {
  const groups = new Map<string, ModelInfo[]>();
  for (const model of models) {
    const provider = model.provider || 'Other';
    if (!groups.has(provider)) {
      groups.set(provider, []);
    }
    groups.get(provider)!.push(model);
  }
  return groups;
};

// Get short display name for model
const getDisplayName = (model: ModelInfo): string => {
  // Remove provider prefix if present
  const name = model.model.split('/').pop() || model.model;
  // Truncate if too long
  return name.length > 25 ? name.substring(0, 22) + '...' : name;
};

const ModelSelector: React.FC<ModelSelectorProps> = ({
  selectedModel,
  onModelChange,
  className = '',
}) => {
  const [models, setModels] = useState<ModelInfo[]>([]);
  const [defaultModel, setDefaultModel] = useState<string>('');
  const [isOpen, setIsOpen] = useState(false);
  const [isLoading, setIsLoading] = useState(true);
  const [error, setError] = useState<string | null>(null);
  const dropdownRef = useRef<HTMLDivElement>(null);

  // Fetch models on mount
  useEffect(() => {
    const fetchModels = async () => {
      try {
        setIsLoading(true);
        const response = await api.getModels();
        setModels(response.models);
        setDefaultModel(response.default_model);

        // If no model selected, select the default
        if (!selectedModel && response.models.length > 0) {
          const defaultModelInfo = response.models.find(m => m.model === response.default_model);
          if (defaultModelInfo) {
            onModelChange(defaultModelInfo);
          } else {
            onModelChange(response.models[0]);
          }
        }
      } catch (e: any) {
        console.error('Failed to fetch models:', e);
        setError(e.message || 'Failed to load models');
      } finally {
        setIsLoading(false);
      }
    };

    fetchModels();
  }, []);

  // Close dropdown when clicking outside
  useEffect(() => {
    const handleClickOutside = (event: MouseEvent) => {
      if (dropdownRef.current && !dropdownRef.current.contains(event.target as Node)) {
        setIsOpen(false);
      }
    };

    document.addEventListener('mousedown', handleClickOutside);
    return () => document.removeEventListener('mousedown', handleClickOutside);
  }, []);

  const groupedModels = groupByProvider(models);

  if (isLoading) {
    return (
      <div className={`inline-flex items-center gap-1.5 px-2 py-1 rounded text-xs bg-surface-700/50 text-surface-400 ${className}`}>
        <svg className="animate-spin h-3 w-3" viewBox="0 0 24 24">
          <circle className="opacity-25" cx="12" cy="12" r="10" stroke="currentColor" strokeWidth="4" fill="none" />
          <path className="opacity-75" fill="currentColor" d="M4 12a8 8 0 018-8V0C5.373 0 0 5.373 0 12h4z" />
        </svg>
        <span className="hidden sm:inline">Loading...</span>
      </div>
    );
  }

  if (error) {
    return (
      <div
        className={`inline-flex items-center gap-1.5 px-2 py-1 rounded text-xs bg-red-500/10 text-red-400 border border-red-500/30 ${className}`}
        title={error}
      >
        <svg className="w-3 h-3" fill="none" viewBox="0 0 24 24" stroke="currentColor">
          <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M12 8v4m0 4h.01M21 12a9 9 0 11-18 0 9 9 0 0118 0z" />
        </svg>
        <span className="hidden sm:inline">Error</span>
      </div>
    );
  }

  return (
    <div className={`relative ${className}`} ref={dropdownRef}>
      {/* Trigger Button */}
      <button
        onClick={() => setIsOpen(!isOpen)}
        className="flex items-center gap-1.5 px-2 py-1 rounded border border-surface-600/50 bg-surface-700/50 hover:bg-surface-600/50 transition-colors text-xs"
      >
        <span className="text-surface-400 hidden sm:inline">Model:</span>
        <span className="text-white font-medium truncate max-w-[120px] sm:max-w-[180px]">
          {selectedModel ? getDisplayName(selectedModel) : 'Select...'}
        </span>
        {selectedModel && selectedModel.max_thinking_tokens > 0 && (
          <span className="px-1 py-0.5 rounded text-[9px] bg-purple-500/20 text-purple-300 hidden sm:inline">
            Think
          </span>
        )}
        <svg
          className={`w-3 h-3 text-surface-400 transition-transform ${isOpen ? 'rotate-180' : ''}`}
          fill="none"
          viewBox="0 0 24 24"
          stroke="currentColor"
        >
          <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M19 9l-7 7-7-7" />
        </svg>
      </button>

      {/* Dropdown Menu */}
      {isOpen && (
        <div className="absolute left-0 top-full mt-1 z-50 w-[320px] sm:w-[400px] max-h-[400px] overflow-auto bg-surface-800 border border-surface-600 rounded-lg shadow-xl">
          {Array.from(groupedModels.entries()).map(([provider, providerModels], index) => (
            <div key={provider}>
              {index > 0 && <div className="border-t border-surface-700" />}
              <div className="px-3 py-1.5 text-[10px] font-medium text-surface-500 uppercase tracking-wider bg-surface-800/50 sticky top-0">
                {provider}
              </div>
              {providerModels.map((model) => {
                const isSelected = selectedModel?.model === model.model;
                const isDefault = model.model === defaultModel;

                return (
                  <button
                    key={model.model}
                    onClick={() => {
                      onModelChange(model);
                      setIsOpen(false);
                    }}
                    className={`w-full text-left px-3 py-2 hover:bg-surface-700/50 transition-colors ${
                      isSelected ? 'bg-accent-500/10 border-l-2 border-accent-500' : ''
                    }`}
                  >
                    <div className="flex items-center justify-between gap-2">
                      <div className="flex items-center gap-2 min-w-0">
                        <span className={`text-sm truncate ${isSelected ? 'text-white font-medium' : 'text-surface-200'}`}>
                          {getDisplayName(model)}
                        </span>
                        {isDefault && (
                          <span className="px-1 py-0.5 rounded text-[9px] bg-green-500/20 text-green-300 flex-shrink-0">
                            Default
                          </span>
                        )}
                      </div>
                      <div className="flex items-center gap-2 text-[10px] text-surface-400 flex-shrink-0">
                        <span className="text-green-400">{formatCost(model.input_cost)}</span>
                        <span>{formatTokens(model.context_limit)} ctx</span>
                        <span className="text-yellow-400">ELO {model.elo}</span>
                      </div>
                    </div>
                    {model.max_thinking_tokens > 0 && (
                      <div className="mt-0.5 text-[10px] text-purple-400 flex items-center gap-1">
                        <svg className="w-3 h-3" fill="none" viewBox="0 0 24 24" stroke="currentColor">
                          <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M9.663 17h4.673M12 3v1m6.364 1.636l-.707.707M21 12h-1M4 12H3m3.343-5.657l-.707-.707m2.828 9.9a5 5 0 117.072 0l-.548.547A3.374 3.374 0 0014 18.469V19a2 2 0 11-4 0v-.531c0-.895-.356-1.754-.988-2.386l-.548-.547z" />
                        </svg>
                        {formatTokens(model.max_thinking_tokens)} thinking tokens
                      </div>
                    )}
                  </button>
                );
              })}
            </div>
          ))}
        </div>
      )}
    </div>
  );
};

export default ModelSelector;
