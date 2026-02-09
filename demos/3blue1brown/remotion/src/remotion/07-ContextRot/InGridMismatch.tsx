import React, { useMemo } from "react";
import { Easing, interpolate, useCurrentFrame, useVideoConfig } from "remotion";
import { BEATS, COLORS, GRID_CONFIG } from "./constants";

/**
 * InGridMismatch shows the context mismatch directly within the grid visualization
 * (as spec describes: red blocks inside context window = irrelevant, green outside = needed but missed)
 * This is an alternative to the split-screen SplitViewMismatch component.
 */
export const InGridMismatch: React.FC = () => {
  const frame = useCurrentFrame();
  const { width, height } = useVideoConfig();

  // Use the same large grid as the end of Part 2
  const gridSize = GRID_CONFIG.XLARGE_SIZE; // 32x32
  const blockSize = 50;

  // Calculate total grid dimensions
  const totalGridWidth = gridSize * blockSize + (gridSize - 1) * GRID_CONFIG.BLOCK_GAP;
  const totalGridHeight = gridSize * blockSize + (gridSize - 1) * GRID_CONFIG.BLOCK_GAP;

  // Grid area
  const gridAreaWidth = width - 200;
  const gridAreaHeight = height - 200;
  const offsetX = 100 + (gridAreaWidth - totalGridWidth) / 2;
  const offsetY = 100 + (gridAreaHeight - totalGridHeight) / 2;

  // Fixed context window size
  const contextWindowSize = 240;
  const contextCenterX = width / 2 + 50;
  const contextCenterY = height / 2 - 30;
  const halfContextSize = contextWindowSize / 2;

  // Get block color
  const getBlockColor = (row: number, col: number) => {
    const seed = row * gridSize + col;
    const colorIndex = seed % COLORS.CODE_BLOCK_COLORS.length;
    return COLORS.CODE_BLOCK_COLORS[colorIndex];
  };

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

  // Determine if a block is relevant (pseudo-random but deterministic)
  const isRelevantBlock = (row: number, col: number) => {
    const seed = (row * 17 + col * 13 + 7) % 100;
    // Relevant blocks are scattered throughout the grid
    return seed < 25; // ~25% of blocks are relevant
  };

  // Animation: fade in from previous view
  const fadeInOpacity = interpolate(
    frame,
    [BEATS.SPLIT_VIEW_START, BEATS.SPLIT_VIEW_START + 45],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.cubic) }
  );

  // Highlight animation: stagger the appearance of red/green highlights
  const highlightProgress = interpolate(
    frame,
    [BEATS.SPLIT_VIEW_START + 30, BEATS.SPLIT_VIEW_START + 75],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.cubic) }
  );

  // Pulse for highlights
  const highlightPulse = Math.sin((frame - BEATS.SPLIT_VIEW_START) * 0.12) * 0.2 + 0.8;

  // Generate the grid of blocks
  const blocks = useMemo(() => {
    const result: React.ReactNode[] = [];

    for (let row = 0; row < gridSize; row++) {
      for (let col = 0; col < gridSize; col++) {
        const x = offsetX + col * (blockSize + GRID_CONFIG.BLOCK_GAP);
        const y = offsetY + row * (blockSize + GRID_CONFIG.BLOCK_GAP);
        const color = getBlockColor(row, col);
        const inContext = isInContext(x, y);
        const isRelevant = isRelevantBlock(row, col);

        // Determine highlight type:
        // - Red: inside context window but irrelevant (AI grabbed wrong code)
        // - Green: outside context window but relevant (AI missed needed code)
        const showRedHighlight = inContext && !isRelevant && highlightProgress > 0;
        const showGreenHighlight = !inContext && isRelevant && highlightProgress > 0;

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
              opacity={inContext ? 1 : 0.3}
            />

            {/* Red highlight for irrelevant code inside context */}
            {showRedHighlight && (
              <rect
                x={x - 2}
                y={y - 2}
                width={blockSize + 4}
                height={blockSize + 4}
                rx={Math.min(GRID_CONFIG.BLOCK_RADIUS + 1, blockSize / 4 + 1)}
                fill="none"
                stroke={COLORS.IRRELEVANT_CODE}
                strokeWidth={3}
                opacity={highlightPulse * highlightProgress}
              />
            )}

            {/* Green highlight for relevant code outside context */}
            {showGreenHighlight && (
              <>
                <rect
                  x={x - 2}
                  y={y - 2}
                  width={blockSize + 4}
                  height={blockSize + 4}
                  rx={Math.min(GRID_CONFIG.BLOCK_RADIUS + 1, blockSize / 4 + 1)}
                  fill="none"
                  stroke={COLORS.RELEVANT_CODE}
                  strokeWidth={3}
                  opacity={highlightPulse * highlightProgress * 0.8}
                />
                {/* Subtle fill to make green blocks more visible */}
                <rect
                  x={x}
                  y={y}
                  width={blockSize}
                  height={blockSize}
                  rx={Math.min(GRID_CONFIG.BLOCK_RADIUS, blockSize / 4)}
                  fill={COLORS.RELEVANT_CODE}
                  opacity={highlightProgress * 0.15}
                />
              </>
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
  }, [gridSize, blockSize, offsetX, offsetY, highlightProgress, highlightPulse, contextCenterX, contextCenterY]);

  // Context window pulse
  const windowPulse = Math.sin(frame * 0.1) * 0.3 + 0.7;

  return (
    <div
      style={{
        position: "absolute",
        top: 0,
        left: 0,
        width: "100%",
        height: "100%",
        opacity: fadeInOpacity,
      }}
    >
      {/* Title */}
      <div
        style={{
          position: "absolute",
          top: 30,
          left: "50%",
          transform: "translateX(-50%)",
          fontFamily: "Inter, system-ui, sans-serif",
          fontSize: 36,
          fontWeight: 700,
          color: COLORS.TITLE,
          textShadow: "0 2px 10px rgba(0,0,0,0.5)",
        }}
      >
        The Context Mismatch Problem
      </div>

      {/* Grid visualization */}
      <div
        style={{
          position: "absolute",
          top: 100,
          left: 100,
          width: gridAreaWidth,
          height: gridAreaHeight,
          overflow: "visible",
        }}
      >
        <svg
          width={gridAreaWidth}
          height={gridAreaHeight}
          style={{ position: "absolute", top: 0, left: 0, overflow: "visible" }}
        >
          <defs>
            {/* Glow filter for context window */}
            <filter id="mismatchContextGlow" x="-50%" y="-50%" width="200%" height="200%">
              <feGaussianBlur in="SourceGraphic" stdDeviation="6" result="blur" />
              <feMerge>
                <feMergeNode in="blur" />
                <feMergeNode in="SourceGraphic" />
              </feMerge>
            </filter>
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
            opacity={windowPulse}
            filter="url(#mismatchContextGlow)"
          />
        </svg>
      </div>

      {/* Legend */}
      <div
        style={{
          position: "absolute",
          bottom: 60,
          left: "50%",
          transform: "translateX(-50%)",
          display: "flex",
          gap: 40,
          padding: "12px 24px",
          backgroundColor: "rgba(26, 26, 46, 0.9)",
          borderRadius: 8,
          opacity: highlightProgress,
        }}
      >
        <div style={{ display: "flex", alignItems: "center", gap: 12 }}>
          <div
            style={{
              width: 20,
              height: 20,
              borderRadius: 4,
              border: `3px solid ${COLORS.IRRELEVANT_CODE}`,
              backgroundColor: "transparent",
            }}
          />
          <span
            style={{
              fontFamily: "Inter, system-ui, sans-serif",
              fontSize: 16,
              color: COLORS.IRRELEVANT_CODE,
            }}
          >
            Inside window: irrelevant code
          </span>
        </div>
        <div style={{ display: "flex", alignItems: "center", gap: 12 }}>
          <div
            style={{
              width: 20,
              height: 20,
              borderRadius: 4,
              border: `3px solid ${COLORS.RELEVANT_CODE}`,
              backgroundColor: `${COLORS.RELEVANT_CODE}40`,
            }}
          />
          <span
            style={{
              fontFamily: "Inter, system-ui, sans-serif",
              fontSize: 16,
              color: COLORS.RELEVANT_CODE,
            }}
          >
            Outside window: needed but missed
          </span>
        </div>
      </div>

      {/* Explanation callout */}
      {highlightProgress > 0.5 && (
        <div
          style={{
            position: "absolute",
            top: 140,
            right: 80,
            maxWidth: 320,
            padding: "16px 20px",
            backgroundColor: "rgba(26, 26, 46, 0.95)",
            borderRadius: 10,
            border: `2px solid ${COLORS.IRRELEVANT_CODE}60`,
            opacity: interpolate(highlightProgress, [0.5, 1], [0, 1]),
          }}
        >
          <div
            style={{
              fontFamily: "Inter, system-ui, sans-serif",
              fontSize: 18,
              fontWeight: 600,
              color: COLORS.TITLE,
              marginBottom: 8,
            }}
          >
            The Problem:
          </div>
          <div
            style={{
              fontFamily: "Inter, system-ui, sans-serif",
              fontSize: 14,
              color: "rgba(255, 255, 255, 0.8)",
              lineHeight: 1.5,
            }}
          >
            AI grabbed <span style={{ color: COLORS.IRRELEVANT_CODE, fontWeight: 600 }}>wrong code</span> inside its tiny window,
            while <span style={{ color: COLORS.RELEVANT_CODE, fontWeight: 600 }}>needed code</span> sits outside, invisible.
          </div>
        </div>
      )}
    </div>
  );
};
