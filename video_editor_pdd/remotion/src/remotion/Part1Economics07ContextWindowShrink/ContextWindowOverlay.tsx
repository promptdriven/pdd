import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  CONTEXT_WINDOW_WIDTH,
  CONTEXT_WINDOW_HEIGHT,
  WINDOW_BORDER_COLOR,
  WINDOW_GLOW_OPACITY,
  WINDOW_GLOW_BLUR,
  WINDOW_TINT_OPACITY,
  CANVAS_WIDTH,
  CANVAS_HEIGHT,
} from "./constants";

/**
 * The fixed-size "context window" overlay.
 * Always centered on the grid (screen center). Never changes size.
 * Has a glowing border and faint interior tint.
 */
export const ContextWindowOverlay: React.FC = () => {
  const frame = useCurrentFrame();

  // Fade in during the first 60 frames
  const opacity = interpolate(frame, [20, 60], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.out(Easing.cubic),
  });

  // Gentle pulse on the glow
  const pulsePhase = Math.sin(frame * 0.03) * 0.5 + 0.5;
  const glowIntensity = WINDOW_GLOW_BLUR + pulsePhase * 4;

  const left = (CANVAS_WIDTH - CONTEXT_WINDOW_WIDTH) / 2;
  const top = (CANVAS_HEIGHT - CONTEXT_WINDOW_HEIGHT) / 2;

  return (
    <div
      style={{
        position: "absolute",
        left,
        top,
        width: CONTEXT_WINDOW_WIDTH,
        height: CONTEXT_WINDOW_HEIGHT,
        opacity,
        border: `2px solid ${WINDOW_BORDER_COLOR}`,
        borderRadius: 4,
        backgroundColor: `rgba(74, 144, 217, ${WINDOW_TINT_OPACITY})`,
        boxShadow: `0 0 ${glowIntensity}px rgba(74, 144, 217, ${WINDOW_GLOW_OPACITY}), inset 0 0 ${glowIntensity * 0.5}px rgba(74, 144, 217, ${WINDOW_GLOW_OPACITY * 0.5})`,
        pointerEvents: "none",
        zIndex: 10,
      }}
    />
  );
};

export default ContextWindowOverlay;
