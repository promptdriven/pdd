import React from "react";
import { Easing, interpolate, useCurrentFrame, useVideoConfig } from "remotion";
import { CodebaseGrid } from "./CodebaseGrid";
import { BEATS, COLORS, GRID_CONFIG, CONTEXT_COVERAGE } from "./constants";

export const ContextWindowVisualization: React.FC = () => {
  const frame = useCurrentFrame();
  const { width, height } = useVideoConfig();

  // Morph-in opacity from debt view
  const morphInOpacity = interpolate(
    frame,
    [BEATS.MORPH_TO_GRID_START, BEATS.MORPH_TO_GRID_END],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.cubic) }
  );

  // Calculate current grid size based on animation phase
  const getGridSize = () => {
    if (frame < BEATS.CODEBASE_GROWTH_START) {
      return GRID_CONFIG.SMALL_SIZE; // 4x4
    }

    // During growth animation: 4 -> 8 -> 16 -> 32
    const growthProgress = interpolate(
      frame,
      [BEATS.CODEBASE_GROWTH_START, BEATS.CODEBASE_GROWTH_END],
      [0, 1],
      { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.inOut(Easing.cubic) }
    );

    if (growthProgress < 0.33) {
      // 4 -> 8
      const t = growthProgress / 0.33;
      return Math.round(GRID_CONFIG.SMALL_SIZE + t * (GRID_CONFIG.MEDIUM_SIZE - GRID_CONFIG.SMALL_SIZE));
    } else if (growthProgress < 0.66) {
      // 8 -> 16
      const t = (growthProgress - 0.33) / 0.33;
      return Math.round(GRID_CONFIG.MEDIUM_SIZE + t * (GRID_CONFIG.LARGE_SIZE - GRID_CONFIG.MEDIUM_SIZE));
    } else {
      // 16 -> 32
      const t = (growthProgress - 0.66) / 0.34;
      return Math.round(GRID_CONFIG.LARGE_SIZE + t * (GRID_CONFIG.XLARGE_SIZE - GRID_CONFIG.LARGE_SIZE));
    }
  };

  // Calculate context coverage percentage
  const getCoveragePercent = () => {
    if (frame < BEATS.CODEBASE_GROWTH_START) {
      return CONTEXT_COVERAGE.SMALL;
    }

    const growthProgress = interpolate(
      frame,
      [BEATS.CODEBASE_GROWTH_START, BEATS.CODEBASE_GROWTH_END],
      [0, 1],
      { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
    );

    if (growthProgress < 0.33) {
      return interpolate(growthProgress, [0, 0.33], [CONTEXT_COVERAGE.SMALL, CONTEXT_COVERAGE.MEDIUM]);
    } else if (growthProgress < 0.66) {
      return interpolate(growthProgress, [0.33, 0.66], [CONTEXT_COVERAGE.MEDIUM, CONTEXT_COVERAGE.LARGE]);
    } else {
      return interpolate(growthProgress, [0.66, 1], [CONTEXT_COVERAGE.LARGE, CONTEXT_COVERAGE.XLARGE]);
    }
  };

  const gridSize = getGridSize();
  const coveragePercent = getCoveragePercent();

  // Fixed context window size in pixels (doesn't change!)
  const FIXED_CONTEXT_WINDOW_SIZE = 240;

  // Grid dimensions for display
  const gridAreaWidth = width - 200;
  const gridAreaHeight = height - 200;

  // Label for current state
  const getStateLabel = () => {
    if (frame < BEATS.CODEBASE_GROWTH_START) {
      return "Small project - AI sees almost everything";
    } else if (frame >= BEATS.LARGE_CODEBASE_START) {
      return "Large project - AI sees through a keyhole";
    }
    return "";
  };

  // Show label during stable states
  const labelOpacity = interpolate(
    frame,
    [
      BEATS.SMALL_CODEBASE_START + 30,
      BEATS.SMALL_CODEBASE_START + 60,
      BEATS.CODEBASE_GROWTH_START - 30,
      BEATS.CODEBASE_GROWTH_START,
    ],
    [0, 1, 1, 0],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  const largeLabelOpacity = interpolate(
    frame,
    [BEATS.LARGE_CODEBASE_START + 30, BEATS.LARGE_CODEBASE_START + 60],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  // Bug flash animation for large codebase
  const showBugs = frame >= BEATS.LARGE_CODEBASE_START;
  const bugMultiplier = frame >= BEATS.LARGE_CODEBASE_START ? Math.floor((frame - BEATS.LARGE_CODEBASE_START) / 30) + 1 : 0;

  // Red flash for irrelevant code in context
  const flashPhase = frame >= BEATS.LARGE_CODEBASE_START
    ? Math.sin((frame - BEATS.LARGE_CODEBASE_START) * 0.15) * 0.5 + 0.5
    : 0;

  return (
    <div
      style={{
        position: "absolute",
        top: 0,
        left: 0,
        width: "100%",
        height: "100%",
        opacity: morphInOpacity,
      }}
    >
      {/* Grid visualization */}
      <div
        style={{
          position: "absolute",
          top: 100,
          left: 100,
          width: gridAreaWidth,
          height: gridAreaHeight,
        }}
      >
        <CodebaseGrid
          gridSize={gridSize}
          width={gridAreaWidth}
          height={gridAreaHeight}
          contextWindowSize={FIXED_CONTEXT_WINDOW_SIZE}
          showBugs={showBugs}
          bugMultiplier={bugMultiplier}
        />
      </div>

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
        The Shrinking Context Window
      </div>

      {/* Coverage counter */}
      <div
        style={{
          position: "absolute",
          top: 120,
          right: 60,
          fontFamily: "Inter, system-ui, sans-serif",
          fontSize: 24,
          fontWeight: 600,
          color: COLORS.CONTEXT_WINDOW_BORDER,
          textShadow: "0 2px 8px rgba(0,0,0,0.8)",
          padding: "12px 20px",
          backgroundColor: "rgba(26, 26, 46, 0.85)",
          borderRadius: 8,
          border: `2px solid ${COLORS.CONTEXT_WINDOW_BORDER}40`,
        }}
      >
        <div style={{ marginBottom: 8, color: COLORS.TITLE, fontSize: 18 }}>
          Context Coverage
        </div>
        <div style={{ fontSize: 48, fontWeight: 700 }}>
          {Math.round(coveragePercent)}%
        </div>
      </div>

      {/* Grid size indicator */}
      <div
        style={{
          position: "absolute",
          bottom: 100,
          left: 60,
          fontFamily: "Inter, system-ui, sans-serif",
          fontSize: 18,
          fontWeight: 500,
          color: "rgba(255, 255, 255, 0.7)",
          textShadow: "0 2px 8px rgba(0,0,0,0.8)",
          padding: "10px 16px",
          backgroundColor: "rgba(26, 26, 46, 0.8)",
          borderRadius: 6,
        }}
      >
        Codebase: {gridSize}x{gridSize} modules ({gridSize * gridSize} total)
      </div>

      {/* State label (small codebase) */}
      {frame < BEATS.CODEBASE_GROWTH_START && labelOpacity > 0 && (
        <div
          style={{
            position: "absolute",
            bottom: 180,
            left: "50%",
            transform: "translateX(-50%)",
            opacity: labelOpacity,
            fontFamily: "Inter, system-ui, sans-serif",
            fontSize: 28,
            fontWeight: 600,
            color: COLORS.RELEVANT_CODE,
            textShadow: "0 2px 10px rgba(0,0,0,0.8)",
            padding: "16px 32px",
            backgroundColor: "rgba(26, 26, 46, 0.9)",
            borderRadius: 10,
            border: `2px solid ${COLORS.RELEVANT_CODE}40`,
          }}
        >
          {getStateLabel()}
        </div>
      )}

      {/* State label (large codebase) */}
      {frame >= BEATS.LARGE_CODEBASE_START && (
        <div
          style={{
            position: "absolute",
            bottom: 180,
            left: "50%",
            transform: "translateX(-50%)",
            opacity: largeLabelOpacity,
            fontFamily: "Inter, system-ui, sans-serif",
            fontSize: 28,
            fontWeight: 600,
            color: COLORS.IRRELEVANT_CODE,
            textShadow: "0 2px 10px rgba(0,0,0,0.8)",
            padding: "16px 32px",
            backgroundColor: "rgba(26, 26, 46, 0.9)",
            borderRadius: 10,
            border: `2px solid ${COLORS.IRRELEVANT_CODE}40`,
          }}
        >
          {getStateLabel()}
        </div>
      )}

      {/* Red flash overlay for large codebase (irrelevant code flash) */}
      {frame >= BEATS.LARGE_CODEBASE_START + 60 && (
        <div
          style={{
            position: "absolute",
            top: 0,
            left: 0,
            width: "100%",
            height: "100%",
            backgroundColor: `rgba(148, 74, 74, ${flashPhase * 0.05})`,
            pointerEvents: "none",
          }}
        />
      )}
    </div>
  );
};
