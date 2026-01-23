import React, { useState } from 'react';
import { ModelInfo } from '../api';
import { formatCost } from '../lib/format';

interface ModelSlidersProps {
  models: ModelInfo[];
  strength: number;
  onStrengthChange: (value: number) => void;
  time: number;
  onTimeChange: (value: number) => void;
  temperature: number;
  onTemperatureChange: (value: number) => void;
  resolvedModel: ModelInfo | null;
}

const ModelSliders: React.FC<ModelSlidersProps> = ({
  models,
  strength,
  onStrengthChange,
  time,
  onTimeChange,
  temperature,
  onTemperatureChange,
  resolvedModel,
}) => {
  const [isExpanded, setIsExpanded] = useState(false);

  // Step size: each step = one model
  const strengthStep = models.length > 1 ? 1 / (models.length - 1) : 0.05;

  return (
    <div className="border-b border-surface-700/50">
      {/* Toggle header */}
      <button
        onClick={() => setIsExpanded(!isExpanded)}
        className="w-full flex items-center justify-between px-3 sm:px-4 py-1.5 hover:bg-surface-700/30 transition-colors text-xs"
      >
        <div className="flex items-center gap-2">
          <svg
            className={`w-3 h-3 text-surface-400 transition-transform duration-200 ${isExpanded ? 'rotate-90' : ''}`}
            fill="none"
            stroke="currentColor"
            viewBox="0 0 24 24"
          >
            <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M9 5l7 7-7 7" />
          </svg>
          <span className="text-surface-300 font-medium">Model Selection</span>
        </div>
        {resolvedModel && (
          <span className="text-surface-400 font-mono text-[10px] sm:text-xs">
            {resolvedModel.model} (ELO {resolvedModel.elo})
          </span>
        )}
      </button>

      {/* Expandable content */}
      {isExpanded && (
        <div className="px-3 sm:px-4 pb-3 pt-1 space-y-3">
          {/* Strength slider */}
          <div className="space-y-1">
            <div className="flex items-center justify-between">
              <label className="text-[10px] sm:text-xs text-surface-400">Strength</label>
              <span className="text-[10px] sm:text-xs font-mono text-white">{strength.toFixed(2)}</span>
            </div>
            <input
              type="range"
              min="0"
              max="1"
              step={strengthStep}
              value={strength}
              onChange={(e) => onStrengthChange(parseFloat(e.target.value))}
              className="w-full h-1.5 bg-surface-700 rounded-full appearance-none cursor-pointer accent-accent-500"
            />
            {resolvedModel && (
              <div className="flex items-center gap-2 text-[10px] text-surface-500">
                <span className="text-accent-400">{resolvedModel.model}</span>
                <span>ELO {resolvedModel.elo}</span>
                <span className="text-green-400">{formatCost(resolvedModel.input_cost)}/M in</span>
              </div>
            )}
          </div>

          {/* Time slider */}
          <div className="space-y-1">
            <div className="flex items-center justify-between">
              <label className="text-[10px] sm:text-xs text-surface-400">Time (reasoning)</label>
              <span className="text-[10px] sm:text-xs font-mono text-white">{time.toFixed(2)}</span>
            </div>
            <input
              type="range"
              min="0"
              max="1"
              step="0.05"
              value={time}
              onChange={(e) => onTimeChange(parseFloat(e.target.value))}
              className="w-full h-1.5 bg-surface-700 rounded-full appearance-none cursor-pointer accent-purple-500"
            />
          </div>

          {/* Temperature slider */}
          <div className="space-y-1">
            <div className="flex items-center justify-between">
              <label className="text-[10px] sm:text-xs text-surface-400">Temperature</label>
              <span className="text-[10px] sm:text-xs font-mono text-white">{temperature.toFixed(1)}</span>
            </div>
            <input
              type="range"
              min="0"
              max="2"
              step="0.1"
              value={temperature}
              onChange={(e) => onTemperatureChange(parseFloat(e.target.value))}
              className="w-full h-1.5 bg-surface-700 rounded-full appearance-none cursor-pointer accent-orange-500"
            />
          </div>
        </div>
      )}
    </div>
  );
};

export default ModelSliders;
