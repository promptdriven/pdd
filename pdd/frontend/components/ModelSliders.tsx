import React, { useState, useRef, useEffect } from 'react';
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
  const [isOpen, setIsOpen] = useState(false);
  const panelRef = useRef<HTMLDivElement>(null);

  // Step size: each step = one model
  const strengthStep = models.length > 1 ? 1 / (models.length - 1) : 0.05;

  // Close on outside click
  useEffect(() => {
    const handleClickOutside = (event: MouseEvent) => {
      if (panelRef.current && !panelRef.current.contains(event.target as Node)) {
        setIsOpen(false);
      }
    };
    if (isOpen) {
      document.addEventListener('mousedown', handleClickOutside);
    }
    return () => document.removeEventListener('mousedown', handleClickOutside);
  }, [isOpen]);

  return (
    <div className="relative border-b border-surface-700/50" ref={panelRef}>
      {/* Compact trigger bar */}
      <button
        onClick={() => setIsOpen(!isOpen)}
        className="w-full flex items-center gap-3 px-3 sm:px-4 py-1.5 hover:bg-surface-700/30 transition-colors text-xs"
      >
        <svg
          className={`w-3 h-3 text-surface-400 transition-transform duration-200 flex-shrink-0 ${isOpen ? 'rotate-90' : ''}`}
          fill="none"
          stroke="currentColor"
          viewBox="0 0 24 24"
        >
          <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M9 5l7 7-7 7" />
        </svg>
        <span className="text-surface-300 font-medium">Model</span>
        {resolvedModel && (
          <>
            <span className="text-surface-500">|</span>
            <span className="text-accent-400 font-mono truncate">{resolvedModel.model}</span>
            <span className="text-surface-500 font-mono">ELO {resolvedModel.elo}</span>
            <span className="text-surface-500">|</span>
            <span className="text-surface-500 font-mono">S:{strength.toFixed(2)}</span>
            <span className="text-surface-500 font-mono">T:{time.toFixed(2)}</span>
            <span className="text-surface-500 font-mono">Temp:{temperature.toFixed(1)}</span>
          </>
        )}
      </button>

      {/* Popover panel — constrained width, anchored left */}
      {isOpen && (
        <div className="absolute left-2 top-full z-40 mt-1 w-80 bg-surface-800 border border-surface-600 rounded-xl shadow-2xl animate-scale-in">
          <div className="p-4 space-y-4">
            {/* Resolved model info */}
            {resolvedModel && (
              <div className="flex items-center justify-between text-xs">
                <span className="text-accent-400 font-mono font-medium truncate">{resolvedModel.model}</span>
                <div className="flex items-center gap-2 text-surface-400 flex-shrink-0 ml-2">
                  <span>ELO {resolvedModel.elo}</span>
                  <span className="text-green-400">{formatCost(resolvedModel.input_cost)}/M</span>
                </div>
              </div>
            )}

            {/* Strength slider */}
            <div className="space-y-1.5">
              <div className="flex items-center justify-between">
                <label className="text-xs text-surface-300 font-medium">Strength</label>
                <span className="text-xs font-mono text-white">{strength.toFixed(2)}</span>
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
            </div>

            {/* Time slider */}
            <div className="space-y-1.5">
              <div className="flex items-center justify-between">
                <label className="text-xs text-surface-300 font-medium">Time (reasoning)</label>
                <span className="text-xs font-mono text-white">{time.toFixed(2)}</span>
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
            <div className="space-y-1.5">
              <div className="flex items-center justify-between">
                <label className="text-xs text-surface-300 font-medium">Temperature</label>
                <span className="text-xs font-mono text-white">{temperature.toFixed(1)}</span>
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
        </div>
      )}
    </div>
  );
};

export default ModelSliders;
