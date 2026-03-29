import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  CONTEXT_WINDOW_WIDTH,
  CONTEXT_WINDOW_HEIGHT,
  CONTEXT_BORDER_COLOR,
  GRID_CENTER_X,
  GRID_CENTER_Y,
} from "./constants";

/**
 * Fixed-size context window overlay that stays the same size
 * while the grid grows beneath it.
 */

const ContextWindowOverlay: React.FC = () => {
  const frame = useCurrentFrame();

  // Visible from frame 0, fully bright by frame 30
  const opacity = interpolate(frame, [0, 30], [0.6, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.out(Easing.quad),
  });

  // Subtle pulse on the glow
  const pulsePhase = Math.sin(frame * 0.04) * 0.5 + 0.5;
  const glowIntensity = 12 + pulsePhase * 6;

  const left = GRID_CENTER_X - CONTEXT_WINDOW_WIDTH / 2;
  const top = GRID_CENTER_Y - CONTEXT_WINDOW_HEIGHT / 2;

  return (
    <div
      style={{
        position: "absolute",
        left,
        top,
        width: CONTEXT_WINDOW_WIDTH,
        height: CONTEXT_WINDOW_HEIGHT,
        border: `2px solid ${CONTEXT_BORDER_COLOR}`,
        backgroundColor: "rgba(74, 144, 217, 0.05)",
        boxShadow: `0 0 ${glowIntensity}px rgba(74, 144, 217, 0.2)`,
        opacity,
        pointerEvents: "none",
        zIndex: 10,
      }}
    />
  );
};

export default ContextWindowOverlay;
