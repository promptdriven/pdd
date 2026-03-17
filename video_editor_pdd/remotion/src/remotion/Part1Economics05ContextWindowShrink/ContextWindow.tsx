import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  GRID_CENTER_X,
  GRID_CENTER_Y,
  CONTEXT_WINDOW_W,
  CONTEXT_WINDOW_H,
  CONTEXT_BORDER_COLOR,
  CONTEXT_GLOW_RADIUS,
  CONTEXT_GLOW_OPACITY,
  CONTEXT_TINT_OPACITY,
  GRID_APPEAR_START,
  GRID_APPEAR_END,
  HOLD_START,
  PULSE_CYCLE,
} from "./constants";

/**
 * ContextWindow — the fixed-size glowing rectangle overlay.
 *
 * Stays the same size while the grid grows underneath, making
 * the "blindspot" viscerally obvious.
 */
export const ContextWindow: React.FC = () => {
  const frame = useCurrentFrame();

  const opacity = interpolate(
    frame,
    [GRID_APPEAR_START, GRID_APPEAR_END],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  // Subtle pulse after hold starts
  let pulseOpacity = 0.6;
  if (frame >= HOLD_START) {
    const pulsePhase =
      ((frame - HOLD_START) % PULSE_CYCLE) / PULSE_CYCLE;
    pulseOpacity = interpolate(
      pulsePhase,
      [0, 0.5, 1],
      [0.5, 0.7, 0.5],
      { easing: Easing.inOut(Easing.sin) }
    );
  }

  const left = GRID_CENTER_X - CONTEXT_WINDOW_W / 2;
  const top = GRID_CENTER_Y - CONTEXT_WINDOW_H / 2;

  return (
    <div
      style={{
        position: "absolute",
        left,
        top,
        width: CONTEXT_WINDOW_W,
        height: CONTEXT_WINDOW_H,
        border: `2px solid ${CONTEXT_BORDER_COLOR}`,
        borderRadius: 4,
        opacity,
        boxShadow: `0 0 ${CONTEXT_GLOW_RADIUS}px rgba(74, 144, 217, ${CONTEXT_GLOW_OPACITY}),
                     inset 0 0 ${CONTEXT_GLOW_RADIUS}px rgba(74, 144, 217, ${CONTEXT_GLOW_OPACITY})`,
        backgroundColor: `rgba(74, 144, 217, ${CONTEXT_TINT_OPACITY})`,
        borderColor: `rgba(74, 144, 217, ${pulseOpacity})`,
        pointerEvents: "none" as const,
      }}
    />
  );
};

export default ContextWindow;
