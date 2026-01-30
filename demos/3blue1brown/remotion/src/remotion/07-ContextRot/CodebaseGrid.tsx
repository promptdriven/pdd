import React, { useMemo } from "react";
import { useCurrentFrame } from "remotion";
import { COLORS, GRID_CONFIG } from "./constants";

interface CodebaseGridProps {
  gridSize: number;
  width: number;
  height: number;
  contextWindowSize?: number; // Fixed pixel size of context window
  showBugs?: boolean;
  bugMultiplier?: number; // How many bugs (scales with codebase)
}

export const CodebaseGrid: React.FC<CodebaseGridProps> = ({
  gridSize,
  width,
  height,
  contextWindowSize = 200,
  showBugs = false,
  bugMultiplier = 1,
}) => {
  const frame = useCurrentFrame();

  // Fixed block size — grid grows physically as gridSize increases
  // This is the key visual: codebase expands while context window stays fixed
  const blockSize = 50;

  // Calculate total grid dimensions
  const totalGridWidth = gridSize * blockSize + (gridSize - 1) * GRID_CONFIG.BLOCK_GAP;
  const totalGridHeight = gridSize * blockSize + (gridSize - 1) * GRID_CONFIG.BLOCK_GAP;

  // Center the grid
  const offsetX = (width - totalGridWidth) / 2;
  const offsetY = (height - totalGridHeight) / 2;

  // Generate consistent random colors for blocks using seed
  const getBlockColor = (row: number, col: number) => {
    const seed = row * gridSize + col;
    const colorIndex = seed % COLORS.CODE_BLOCK_COLORS.length;
    return COLORS.CODE_BLOCK_COLORS[colorIndex];
  };

  // Determine if a block should have a bug
  const hasBug = (row: number, col: number) => {
    if (!showBugs) return false;
    const seed = (row * gridSize + col) * 17 + 13;
    // More bugs as codebase grows
    const bugThreshold = 0.95 - (bugMultiplier * 0.01);
    return (seed % 100) / 100 > bugThreshold;
  };

  // Calculate context window bounds (fixed size, centered slightly off-center)
  const contextCenterX = width / 2 + 50;
  const contextCenterY = height / 2 - 30;
  const halfContextSize = contextWindowSize / 2;

  // Check if a block is inside the context window
  const isInContext = (blockX: number, blockY: number) => {
    const blockCenterX = blockX + blockSize / 2;
    const blockCenterY = blockY + blockSize / 2;
    return (
      blockCenterX >= contextCenterX - halfContextSize &&
      blockCenterX <= contextCenterX + halfContextSize &&
      blockCenterY >= contextCenterY - halfContextSize &&
      blockCenterY <= contextCenterY + halfContextSize
    );
  };

  // Generate the grid of blocks
  const blocks = useMemo(() => {
    const result: React.ReactNode[] = [];

    for (let row = 0; row < gridSize; row++) {
      for (let col = 0; col < gridSize; col++) {
        const x = offsetX + col * (blockSize + GRID_CONFIG.BLOCK_GAP);
        const y = offsetY + row * (blockSize + GRID_CONFIG.BLOCK_GAP);
        const color = getBlockColor(row, col);
        const inContext = isInContext(x, y);
        const bug = hasBug(row, col);

        result.push(
          <g key={`block-${row}-${col}`}>
            {/* Block background */}
            <rect
              x={x}
              y={y}
              width={blockSize}
              height={blockSize}
              rx={Math.min(GRID_CONFIG.BLOCK_RADIUS, blockSize / 4)}
              fill={color}
              opacity={inContext ? 1 : 0.4}
              style={{
                transition: "opacity 0.2s ease",
              }}
            />

            {/* Bug indicator (small red dot) */}
            {bug && (
              <circle
                cx={x + blockSize - Math.max(3, blockSize * 0.15)}
                cy={y + Math.max(3, blockSize * 0.15)}
                r={Math.max(2, blockSize * 0.1)}
                fill="#EF4444"
                opacity={0.9}
              />
            )}

            {/* Code lines representation (only for larger blocks) */}
            {blockSize > 15 && (
              <>
                <rect
                  x={x + blockSize * 0.15}
                  y={y + blockSize * 0.2}
                  width={blockSize * 0.6}
                  height={Math.max(1, blockSize * 0.08)}
                  rx={1}
                  fill="rgba(255, 255, 255, 0.2)"
                />
                <rect
                  x={x + blockSize * 0.15}
                  y={y + blockSize * 0.4}
                  width={blockSize * 0.45}
                  height={Math.max(1, blockSize * 0.08)}
                  rx={1}
                  fill="rgba(255, 255, 255, 0.15)"
                />
                <rect
                  x={x + blockSize * 0.15}
                  y={y + blockSize * 0.6}
                  width={blockSize * 0.55}
                  height={Math.max(1, blockSize * 0.08)}
                  rx={1}
                  fill="rgba(255, 255, 255, 0.15)"
                />
              </>
            )}
          </g>
        );
      }
    }

    return result;
  }, [gridSize, blockSize, offsetX, offsetY, showBugs, bugMultiplier, contextCenterX, contextCenterY, contextWindowSize]);

  // Pulse animation for context window border
  const pulsePhase = Math.sin(frame * 0.1) * 0.3 + 0.7;

  return (
    <svg
      width={width}
      height={height}
      style={{ position: "absolute", top: 0, left: 0, overflow: "visible" }}
    >
      <defs>
        {/* Glow filter for context window */}
        <filter id="contextGlow" x="-50%" y="-50%" width="200%" height="200%">
          <feGaussianBlur in="SourceGraphic" stdDeviation="6" result="blur" />
          <feMerge>
            <feMergeNode in="blur" />
            <feMergeNode in="SourceGraphic" />
          </feMerge>
        </filter>

        {/* Clip path for context window interior */}
        <clipPath id="contextClip">
          <rect
            x={contextCenterX - halfContextSize}
            y={contextCenterY - halfContextSize}
            width={contextWindowSize}
            height={contextWindowSize}
            rx={8}
          />
        </clipPath>
      </defs>

      {/* All blocks */}
      {blocks}

      {/* Context window border with glow */}
      <rect
        x={contextCenterX - halfContextSize}
        y={contextCenterY - halfContextSize}
        width={contextWindowSize}
        height={contextWindowSize}
        rx={8}
        fill="none"
        stroke={COLORS.CONTEXT_WINDOW_BORDER}
        strokeWidth={3}
        opacity={pulsePhase}
        filter="url(#contextGlow)"
      />

      {/* Inner highlight border */}
      <rect
        x={contextCenterX - halfContextSize + 4}
        y={contextCenterY - halfContextSize + 4}
        width={contextWindowSize - 8}
        height={contextWindowSize - 8}
        rx={6}
        fill="none"
        stroke={COLORS.CONTEXT_WINDOW_BORDER}
        strokeWidth={1}
        opacity={0.3}
      />
    </svg>
  );
};
