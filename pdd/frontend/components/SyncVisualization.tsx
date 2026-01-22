/**
 * SyncVisualization - Animated visualization of sync operations for remote mode.
 *
 * Renders a TUI-like visual with boxes for prompt, code, example, and tests,
 * connected by animated SVG paths showing the current operation flow.
 */

import React, { useEffect, useState, useRef, useMemo } from 'react';
import { SyncState } from '../types';

interface SyncVisualizationProps {
  state: SyncState;
}

// Color palette
const COLORS = {
  background: '#0A0A23',
  cyan: '#00D8FF',
  purple: '#8C47FF',
  green: '#18C07A',
  magenta: '#FF2AA6',
  red: '#FF4444',
  white: '#F1F5F9',
};

// Operation to arrow path mapping
type ArrowDirection = 'prompt-code' | 'prompt-example' | 'prompt-tests' | 'code-tests' | 'code-example' | 'code-prompt' | 'none' | 'all-pulse';

function getArrowForOperation(operation: string): { path: ArrowDirection; bidirectional: boolean } {
  switch (operation) {
    case 'generate': return { path: 'prompt-code', bidirectional: false };
    case 'example': return { path: 'prompt-example', bidirectional: false };
    case 'test': return { path: 'prompt-tests', bidirectional: false };
    case 'fix': return { path: 'code-tests', bidirectional: true };
    case 'crash':
    case 'verify': return { path: 'code-example', bidirectional: true };
    case 'update': return { path: 'code-prompt', bidirectional: false };
    case 'auto-deps': return { path: 'none', bidirectional: false };
    case 'checking':
    case 'initializing':
    case 'synced': return { path: 'all-pulse', bidirectional: false };
    default: return { path: 'none', bidirectional: false };
  }
}

// Get which box is "active" for a given operation
function getActiveBox(operation: string): string | null {
  switch (operation) {
    case 'generate':
    case 'update': return 'code';
    case 'example': return 'example';
    case 'test': return 'tests';
    case 'fix': return 'code';
    case 'crash':
    case 'verify': return 'code';
    case 'auto-deps': return 'prompt';
    case 'checking':
    case 'initializing': return null;
    default: return null;
  }
}

// Format elapsed time as HH:MM:SS
function formatElapsed(seconds: number): string {
  const h = Math.floor(seconds / 3600);
  const m = Math.floor((seconds % 3600) / 60);
  const s = Math.floor(seconds % 60);
  if (h > 0) return `${h.toString().padStart(2, '0')}:${m.toString().padStart(2, '0')}:${s.toString().padStart(2, '0')}`;
  return `${m.toString().padStart(2, '0')}:${s.toString().padStart(2, '0')}`;
}

// Get basename from full path
function getBasename(filepath: string): string {
  const parts = filepath.split('/');
  return parts[parts.length - 1] || filepath;
}

const SyncVisualization: React.FC<SyncVisualizationProps> = ({ state }) => {
  const [localElapsed, setLocalElapsed] = useState(state.elapsedSeconds);
  const [animDirection, setAnimDirection] = useState<'forward' | 'reverse'>('forward');
  const [prevOperation, setPrevOperation] = useState(state.operation);
  const [flashBox, setFlashBox] = useState<string | null>(null);
  const startTimeRef = useRef<number>(Date.now() - state.elapsedSeconds * 1000);

  // Update local elapsed timer
  useEffect(() => {
    if (state.status !== 'running') return;
    const interval = setInterval(() => {
      setLocalElapsed(Math.floor((Date.now() - startTimeRef.current) / 1000));
    }, 1000);
    return () => clearInterval(interval);
  }, [state.status]);

  // Sync elapsed from backend updates
  useEffect(() => {
    startTimeRef.current = Date.now() - state.elapsedSeconds * 1000;
  }, [state.elapsedSeconds]);

  // Toggle animation direction for bidirectional operations
  const arrowInfo = useMemo(() => getArrowForOperation(state.operation), [state.operation]);
  useEffect(() => {
    if (!arrowInfo.bidirectional) return;
    const interval = setInterval(() => {
      setAnimDirection(d => d === 'forward' ? 'reverse' : 'forward');
    }, 2500);
    return () => clearInterval(interval);
  }, [arrowInfo.bidirectional]);

  // Detect operation changes for flash animation
  useEffect(() => {
    if (state.operation !== prevOperation) {
      const activeBox = getActiveBox(state.operation);
      if (activeBox) {
        setFlashBox(activeBox);
        setTimeout(() => setFlashBox(null), 300);
      }
      setPrevOperation(state.operation);
    }
  }, [state.operation, prevOperation]);

  const activeBox = getActiveBox(state.operation);
  const isCompleted = state.status === 'completed';
  const isFailed = state.status === 'failed';
  const isRunning = state.status === 'running';

  // Cost warning threshold
  const costWarning = state.budget && state.cost > state.budget * 0.8;

  // Box positions for SVG paths (relative to SVG viewBox)
  // SVG viewBox is 400x300
  const positions = {
    prompt: { x: 200, y: 70 },
    code: { x: 100, y: 220 },
    example: { x: 200, y: 220 },
    tests: { x: 300, y: 220 },
  };

  // Generate SVG path between two points
  function getPath(from: { x: number; y: number }, to: { x: number; y: number }): string {
    const midY = (from.y + to.y) / 2;
    return `M ${from.x} ${from.y + 25} C ${from.x} ${midY}, ${to.x} ${midY}, ${to.x} ${to.y - 25}`;
  }

  // Get the SVG path for the current operation
  function getCurrentPath(): string | null {
    switch (arrowInfo.path) {
      case 'prompt-code': return getPath(positions.prompt, positions.code);
      case 'prompt-example': return getPath(positions.prompt, positions.example);
      case 'prompt-tests': return getPath(positions.prompt, positions.tests);
      case 'code-tests': return getPath(positions.code, positions.tests);
      case 'code-example': return getPath(positions.code, positions.example);
      case 'code-prompt': return getPath(positions.code, positions.prompt);
      default: return null;
    }
  }

  const currentPath = getCurrentPath();

  // Unique IDs for SVG elements
  const pathId = `sync-path-${state.basename}`;
  const glowId = `sync-glow-${state.basename}`;

  return (
    <div
      className="relative flex flex-col mx-auto rounded-xl overflow-hidden border"
      style={{
        minWidth: 400,
        maxWidth: 700,
        background: COLORS.background,
        borderColor: `rgba(0, 216, 255, 0.15)`,
        backdropFilter: 'blur(8px)',
      }}
    >
      {/* Background dot grid pattern */}
      <div
        className="absolute inset-0 pointer-events-none"
        style={{
          backgroundImage: `radial-gradient(circle, rgba(0, 216, 255, 0.03) 1px, transparent 1px)`,
          backgroundSize: '20px 20px',
        }}
      />

      {/* Scanline overlay */}
      <div
        className="absolute inset-0 pointer-events-none"
        style={{
          backgroundImage: 'repeating-linear-gradient(0deg, transparent, transparent 2px, rgba(0, 216, 255, 0.015) 2px, rgba(0, 216, 255, 0.015) 4px)',
          opacity: 0.3,
        }}
      />

      {/* Header */}
      <div
        className="relative flex items-center justify-between px-4 py-3 border-b"
        style={{ borderColor: `rgba(0, 216, 255, 0.15)` }}
      >
        <div className="flex items-center gap-2">
          <span style={{ color: COLORS.cyan, fontSize: '14px' }}>&#10022;</span>
          <span className="text-sm font-medium" style={{ color: COLORS.white }}>
            Prompt Driven Development
          </span>
        </div>
        <div className="flex items-center gap-2">
          {isCompleted && (
            <span className="text-xs font-bold uppercase" style={{ color: COLORS.green }}>
              Completed
            </span>
          )}
          {isFailed && (
            <span className="text-xs font-bold uppercase" style={{ color: COLORS.red }}>
              Failed
            </span>
          )}
          {isRunning && (
            <span
              className="text-xs font-bold uppercase"
              style={{
                color: COLORS.cyan,
                animation: 'syncPulse 2s ease-in-out infinite',
              }}
            >
              {state.operation}
            </span>
          )}
        </div>
      </div>

      {/* Main visualization area */}
      <div className="relative flex-1 p-4" style={{ minHeight: 280 }}>
        {/* SVG layer for connections */}
        <svg
          viewBox="0 0 400 300"
          className="absolute inset-0 w-full h-full pointer-events-none"
          style={{ padding: '16px' }}
        >
          <defs>
            <filter id={glowId}>
              <feGaussianBlur stdDeviation="3" result="coloredBlur" />
              <feMerge>
                <feMergeNode in="coloredBlur" />
                <feMergeNode in="SourceGraphic" />
              </feMerge>
            </filter>
          </defs>

          {/* Static connection lines (always visible) */}
          <path
            d={getPath(positions.prompt, positions.code)}
            fill="none"
            stroke={COLORS.cyan}
            strokeWidth="1.5"
            opacity={arrowInfo.path === 'prompt-code' || arrowInfo.path === 'code-prompt' ? 0.8 : 0.2}
            style={{ transition: 'opacity 0.5s ease' }}
          />
          <path
            d={getPath(positions.prompt, positions.example)}
            fill="none"
            stroke={COLORS.cyan}
            strokeWidth="1.5"
            opacity={arrowInfo.path === 'prompt-example' ? 0.8 : 0.2}
            style={{ transition: 'opacity 0.5s ease' }}
          />
          <path
            d={getPath(positions.prompt, positions.tests)}
            fill="none"
            stroke={COLORS.cyan}
            strokeWidth="1.5"
            opacity={arrowInfo.path === 'prompt-tests' ? 0.8 : 0.2}
            style={{ transition: 'opacity 0.5s ease' }}
          />
          <path
            d={getPath(positions.code, positions.tests)}
            fill="none"
            stroke={COLORS.cyan}
            strokeWidth="1.5"
            opacity={arrowInfo.path === 'code-tests' ? 0.8 : 0.2}
            style={{ transition: 'opacity 0.5s ease' }}
          />
          <path
            d={getPath(positions.code, positions.example)}
            fill="none"
            stroke={COLORS.cyan}
            strokeWidth="1.5"
            opacity={arrowInfo.path === 'code-example' ? 0.8 : 0.2}
            style={{ transition: 'opacity 0.5s ease' }}
          />

          {/* Junction dots */}
          <circle cx={positions.prompt.x} cy={positions.prompt.y + 25} r="2" fill={COLORS.cyan} opacity="0.4" />
          <circle cx={positions.code.x} cy={positions.code.y - 25} r="2" fill={COLORS.cyan} opacity="0.4" />
          <circle cx={positions.example.x} cy={positions.example.y - 25} r="2" fill={COLORS.cyan} opacity="0.4" />
          <circle cx={positions.tests.x} cy={positions.tests.y - 25} r="2" fill={COLORS.cyan} opacity="0.4" />

          {/* Animated traveling dot */}
          {currentPath && isRunning && (
            <>
              <path id={pathId} d={currentPath} fill="none" stroke="none" />
              {/* Main dot */}
              <circle r="5" fill={COLORS.cyan} filter={`url(#${glowId})`}>
                <animateMotion
                  dur="2.5s"
                  repeatCount="indefinite"
                  keyPoints={animDirection === 'reverse' ? '1;0' : '0;1'}
                  keyTimes="0;1"
                  calcMode="spline"
                  keySplines="0.42 0 0.58 1"
                >
                  <mpath href={`#${pathId}`} />
                </animateMotion>
              </circle>
              {/* Trail dot 1 */}
              <circle r="3" fill={COLORS.cyan} opacity="0.5">
                <animateMotion
                  dur="2.5s"
                  repeatCount="indefinite"
                  keyPoints={animDirection === 'reverse' ? '1;0' : '0;1'}
                  keyTimes="0;1"
                  calcMode="spline"
                  keySplines="0.42 0 0.58 1"
                  begin="-0.15s"
                >
                  <mpath href={`#${pathId}`} />
                </animateMotion>
              </circle>
              {/* Trail dot 2 */}
              <circle r="2" fill={COLORS.cyan} opacity="0.3">
                <animateMotion
                  dur="2.5s"
                  repeatCount="indefinite"
                  keyPoints={animDirection === 'reverse' ? '1;0' : '0;1'}
                  keyTimes="0;1"
                  calcMode="spline"
                  keySplines="0.42 0 0.58 1"
                  begin="-0.3s"
                >
                  <mpath href={`#${pathId}`} />
                </animateMotion>
              </circle>
            </>
          )}
        </svg>

        {/* Box overlays positioned absolutely */}
        <div className="relative w-full h-full" style={{ minHeight: 260 }}>
          {/* Prompt box - top center */}
          <BoxNode
            label="Prompt"
            emoji="&#x1F4E6;"
            filepath={getBasename(state.paths.prompt)}
            color={COLORS.purple}
            isActive={activeBox === 'prompt'}
            isFlashing={flashBox === 'prompt'}
            isCompleted={isCompleted}
            isFailed={isFailed && activeBox === 'prompt'}
            isPulsing={state.operation === 'auto-deps'}
            allPulsing={arrowInfo.path === 'all-pulse' && isRunning}
            style={{
              position: 'absolute',
              top: '5%',
              left: '50%',
              transform: 'translateX(-50%)',
            }}
          />

          {/* Code box - bottom left */}
          <BoxNode
            label="Code"
            emoji="&#x1F528;"
            filepath={getBasename(state.paths.code)}
            color={COLORS.cyan}
            isActive={activeBox === 'code'}
            isFlashing={flashBox === 'code'}
            isCompleted={isCompleted}
            isFailed={isFailed && activeBox === 'code'}
            allPulsing={arrowInfo.path === 'all-pulse' && isRunning}
            style={{
              position: 'absolute',
              bottom: '5%',
              left: '8%',
            }}
          />

          {/* Example box - bottom center */}
          <BoxNode
            label="Example"
            emoji="&#x1F331;"
            filepath={getBasename(state.paths.example)}
            color={COLORS.green}
            isActive={activeBox === 'example'}
            isFlashing={flashBox === 'example'}
            isCompleted={isCompleted}
            isFailed={isFailed && activeBox === 'example'}
            allPulsing={arrowInfo.path === 'all-pulse' && isRunning}
            style={{
              position: 'absolute',
              bottom: '5%',
              left: '50%',
              transform: 'translateX(-50%)',
            }}
          />

          {/* Tests box - bottom right */}
          <BoxNode
            label="Tests"
            emoji="&#x1F9EA;"
            filepath={getBasename(state.paths.tests)}
            color={COLORS.magenta}
            isActive={activeBox === 'tests'}
            isFlashing={flashBox === 'tests'}
            isCompleted={isCompleted}
            isFailed={isFailed && activeBox === 'tests'}
            allPulsing={arrowInfo.path === 'all-pulse' && isRunning}
            style={{
              position: 'absolute',
              bottom: '5%',
              right: '8%',
            }}
          />
        </div>
      </div>

      {/* Footer */}
      <div
        className="relative flex items-center justify-between px-4 py-2.5 border-t text-xs font-mono"
        style={{ borderColor: `rgba(0, 216, 255, 0.15)` }}
      >
        <span style={{ color: COLORS.cyan, opacity: 0.6 }}>
          {state.basename}
        </span>
        <span style={{ color: COLORS.cyan, opacity: 0.6 }}>
          {formatElapsed(isRunning ? localElapsed : state.elapsedSeconds)}
        </span>
        <span style={{ color: costWarning ? COLORS.magenta : COLORS.cyan, opacity: 0.6 }}>
          ${state.cost.toFixed(2)}
          {state.budget !== null && ` / $${state.budget.toFixed(2)}`}
        </span>
      </div>

      {/* Injected keyframe styles */}
      <style>{`
        @keyframes syncPulse {
          0%, 100% { opacity: 1; }
          50% { opacity: 0.4; }
        }
        @keyframes syncBounce {
          0%, 100% { transform: translateY(0); }
          50% { transform: translateY(-2px); }
        }
        @keyframes syncFlash {
          0% { transform: scale(1.03); }
          100% { transform: scale(1); }
        }
        @keyframes syncShake {
          0%, 100% { transform: translateX(0); }
          25% { transform: translateX(-3px); }
          75% { transform: translateX(3px); }
        }
        @keyframes syncGlowPulse {
          0%, 100% { box-shadow: 0 0 12px rgba(140, 71, 255, 0.3); }
          50% { box-shadow: 0 0 24px rgba(140, 71, 255, 0.6), 0 0 48px rgba(140, 71, 255, 0.3); }
        }
        @keyframes syncAllPulse {
          0%, 100% { opacity: 0.7; }
          50% { opacity: 1; }
        }
      `}</style>
    </div>
  );
};

// Individual box node component
interface BoxNodeProps {
  label: string;
  emoji: string;
  filepath: string;
  color: string;
  isActive: boolean;
  isFlashing: boolean;
  isCompleted: boolean;
  isFailed: boolean;
  isPulsing?: boolean;
  allPulsing?: boolean;
  style: React.CSSProperties;
}

const BoxNode: React.FC<BoxNodeProps> = ({
  label,
  emoji,
  filepath,
  color,
  isActive,
  isFlashing,
  isCompleted,
  isFailed,
  isPulsing,
  allPulsing,
  style,
}) => {
  const boxColor = isFailed ? COLORS.red : isCompleted ? COLORS.green : color;

  const boxShadow = isActive
    ? `0 0 20px rgba(${hexToRgb(boxColor)}, 0.5), 0 0 40px rgba(${hexToRgb(boxColor)}, 0.2)`
    : `0 0 12px rgba(${hexToRgb(boxColor)}, 0.15)`;

  const animationStyle: React.CSSProperties = {};
  if (isFlashing) {
    animationStyle.animation = 'syncFlash 0.3s ease-out';
  }
  if (isFailed) {
    animationStyle.animation = 'syncShake 0.5s ease-out';
  }
  if (isPulsing) {
    animationStyle.animation = 'syncGlowPulse 1.5s ease-in-out infinite';
  }
  if (allPulsing) {
    animationStyle.animation = 'syncAllPulse 2s ease-in-out infinite';
  }

  return (
    <div
      style={{
        ...style,
        ...animationStyle,
        width: 110,
        padding: '10px 8px',
        borderRadius: 8,
        border: `2px solid ${boxColor}`,
        background: `rgba(${hexToRgb(boxColor)}, 0.08)`,
        boxShadow,
        transition: 'box-shadow 0.5s ease, border-color 0.5s ease',
        textAlign: 'center',
      }}
    >
      <div
        style={{
          fontSize: '1.2em',
          marginBottom: 4,
          animation: isActive ? 'syncBounce 0.6s ease-in-out infinite' : 'none',
        }}
        dangerouslySetInnerHTML={{ __html: emoji }}
      />
      <div
        style={{
          fontSize: 11,
          fontWeight: 600,
          color: boxColor,
          marginBottom: 3,
        }}
      >
        {label}
      </div>
      <div
        className="font-mono truncate"
        style={{
          fontSize: 10,
          color: COLORS.cyan,
          opacity: 0.7,
          maxWidth: 94,
          margin: '0 auto',
        }}
        title={filepath}
      >
        {filepath}
      </div>
    </div>
  );
};

// Helper: convert hex color to r,g,b string
function hexToRgb(hex: string): string {
  const result = /^#?([a-f\d]{2})([a-f\d]{2})([a-f\d]{2})$/i.exec(hex);
  if (!result) return '0, 0, 0';
  return `${parseInt(result[1], 16)}, ${parseInt(result[2], 16)}, ${parseInt(result[3], 16)}`;
}

export default SyncVisualization;
