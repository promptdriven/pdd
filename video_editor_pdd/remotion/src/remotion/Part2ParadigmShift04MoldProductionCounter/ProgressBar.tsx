import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  PROGRESS_BAR_WIDTH,
  PROGRESS_BAR_HEIGHT,
  PROGRESS_BAR_X,
  PROGRESS_BAR_Y,
  TRACK_COLOR,
  FILL_GRADIENT_START,
  FILL_GRADIENT_END,
  TOTAL_FRAMES,
} from "./constants";

/**
 * A horizontal progress bar that fills from left to right as the counter climbs.
 * Uses easeInOut(cubic) over the full duration.
 */
export const ProgressBar: React.FC = () => {
  const frame = useCurrentFrame();

  const fillFraction = interpolate(frame, [0, TOTAL_FRAMES - 1], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.inOut(Easing.cubic),
  });

  const fillWidth = fillFraction * PROGRESS_BAR_WIDTH;

  // Subtle glow that increases as bar fills
  const glowIntensity = interpolate(fillFraction, [0, 0.5, 1], [0, 0.3, 0.6], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
  });

  return (
    <div
      style={{
        position: "absolute",
        left: PROGRESS_BAR_X,
        top: PROGRESS_BAR_Y,
        width: PROGRESS_BAR_WIDTH,
        height: PROGRESS_BAR_HEIGHT,
        backgroundColor: TRACK_COLOR,
        borderRadius: PROGRESS_BAR_HEIGHT / 2,
        overflow: "hidden",
      }}
    >
      {/* Fill bar with gradient */}
      <div
        style={{
          position: "absolute",
          left: 0,
          top: 0,
          width: fillWidth,
          height: PROGRESS_BAR_HEIGHT,
          background: `linear-gradient(90deg, ${FILL_GRADIENT_START}, ${FILL_GRADIENT_END})`,
          borderRadius: PROGRESS_BAR_HEIGHT / 2,
          boxShadow: `0 0 ${12 * glowIntensity}px rgba(74, 144, 217, ${glowIntensity})`,
        }}
      />
    </div>
  );
};

export default ProgressBar;
