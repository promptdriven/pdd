import React from "react";
import {
  AbsoluteFill,
  useCurrentFrame,
  interpolate,
  Easing,
} from "remotion";
import {
  BG_COLOR,
  GROWTH_STAGES,
} from "./constants";
import CodeBlockGrid from "./CodeBlockGrid";
import ContextWindowOverlay from "./ContextWindowOverlay";
import CoverageCounter from "./CoverageCounter";
import MismatchHighlights from "./MismatchHighlights";

export const defaultPart1Economics07ContextWindowShrinkProps = {};

/**
 * Section 1.7: Context Window Shrink
 *
 * Demonstrates how a fixed-size context window covers less and less
 * of a growing codebase, from 80% at 4×4 down to 2% at 32×32.
 *
 * Duration: 1560 frames (52s @ 30fps)
 */

/**
 * Determines the current growth stage and transition progress.
 */
function useGridStage(frame: number) {
  // Find which stage we're currently in or transitioning to
  let currentStageIndex = 0;
  let transitionProgress = 1; // 1 = fully in current stage
  let previousGridSize = GROWTH_STAGES[0].gridSize;

  for (let i = GROWTH_STAGES.length - 1; i >= 0; i--) {
    const stage = GROWTH_STAGES[i];
    if (frame >= stage.startFrame) {
      currentStageIndex = i;

      // Calculate transition progress within this stage's transition period
      const framesIntoStage = frame - stage.startFrame;
      if (framesIntoStage < stage.transitionFrames) {
        transitionProgress = interpolate(
          framesIntoStage,
          [0, stage.transitionFrames],
          [0, 1],
          {
            extrapolateLeft: "clamp",
            extrapolateRight: "clamp",
            easing: Easing.inOut(Easing.cubic),
          }
        );
      } else {
        transitionProgress = 1;
      }

      previousGridSize =
        i > 0 ? GROWTH_STAGES[i - 1].gridSize : GROWTH_STAGES[0].gridSize;
      break;
    }
  }

  return {
    currentStageIndex,
    currentGridSize: GROWTH_STAGES[currentStageIndex].gridSize,
    previousGridSize,
    transitionProgress,
  };
}

export const Part1Economics07ContextWindowShrink: React.FC = () => {
  const frame = useCurrentFrame();

  const { currentStageIndex, currentGridSize, previousGridSize, transitionProgress } =
    useGridStage(frame);

  // Title text that fades in early and out after a few seconds
  const titleOpacity = interpolate(frame, [0, 20, 120, 160], [0.8, 0.9, 0.9, 0], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
  });

  return (
    <AbsoluteFill
      style={{
        backgroundColor: BG_COLOR,
        overflow: "hidden",
      }}
    >
      {/* Section title */}
      <div
        style={{
          position: "absolute",
          top: 40,
          left: 0,
          width: "100%",
          textAlign: "center",
          opacity: titleOpacity,
          zIndex: 30,
        }}
      >
        <span
          style={{
            fontFamily: "Inter, sans-serif",
            fontSize: 28,
            fontWeight: 600,
            color: "#E2E8F0",
            letterSpacing: 1,
          }}
        >
          Codebase Growth vs. Fixed Context Window
        </span>
      </div>

      {/* Growing code block grid */}
      <CodeBlockGrid
        currentGridSize={currentGridSize}
        previousGridSize={previousGridSize}
        transitionProgress={transitionProgress}
      />

      {/* Fixed-size context window overlay */}
      <ContextWindowOverlay />

      {/* Coverage percentage counter */}
      <CoverageCounter
        currentStageIndex={currentStageIndex}
        transitionProgress={transitionProgress}
      />

      {/* Red/green mismatch highlights (Phase 3, from frame 720) */}
      <MismatchHighlights />

      {/* Grid size label at bottom */}
      <GridSizeLabel currentGridSize={currentGridSize} />
    </AbsoluteFill>
  );
};

/**
 * Shows the current grid dimensions (e.g., "32×32 blocks") at the bottom.
 */
const GridSizeLabel: React.FC<{
  currentGridSize: number;
}> = ({ currentGridSize }) => {
  const frame = useCurrentFrame();

  const opacity = interpolate(frame, [0, 20], [0.6, 0.85], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
  });

  return (
    <div
      style={{
        position: "absolute",
        bottom: 50,
        left: 0,
        width: "100%",
        textAlign: "center",
        opacity,
        zIndex: 20,
      }}
    >
      <span
        style={{
          fontFamily: "Inter, sans-serif",
          fontSize: 18,
          fontWeight: 500,
          color: "#94A3B8",
        }}
      >
        {currentGridSize}×{currentGridSize} code blocks
      </span>
    </div>
  );
};

export default Part1Economics07ContextWindowShrink;
