// ContextWindow.tsx — The fixed-size "context window" overlay that hovers over the grid.
// Size stays constant (280×240) while the grid grows beneath it, emphasizing the mismatch.

import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import {
  CTX_WINDOW_WIDTH,
  CTX_WINDOW_HEIGHT,
  CTX_BORDER_COLOR,
  CTX_BORDER_WIDTH,
  CTX_GLOW_OPACITY,
  CTX_GLOW_BLUR,
  CTX_FILL_OPACITY,
  GRID_CENTER_X,
  GRID_CENTER_Y,
} from './constants';

export const ContextWindow: React.FC = () => {
  const frame = useCurrentFrame();

  // Fade in over frames 20–60
  const opacity = interpolate(frame, [20, 60], [0, 1], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.quad),
  });

  // Slight gentle pulse on the glow
  const pulsePhase = Math.sin(frame * 0.04) * 0.5 + 0.5; // 0 → 1 oscillation
  const glowBlur = CTX_GLOW_BLUR + pulsePhase * 4;
  const glowOpacity = CTX_GLOW_OPACITY + pulsePhase * 0.05;

  const left = GRID_CENTER_X - CTX_WINDOW_WIDTH / 2;
  const top = GRID_CENTER_Y - CTX_WINDOW_HEIGHT / 2;

  return (
    <div
      style={{
        position: 'absolute',
        left,
        top,
        width: CTX_WINDOW_WIDTH,
        height: CTX_WINDOW_HEIGHT,
        opacity,
        border: `${CTX_BORDER_WIDTH}px solid ${CTX_BORDER_COLOR}`,
        borderRadius: 4,
        backgroundColor: `rgba(74, 144, 217, ${CTX_FILL_OPACITY})`,
        boxShadow: `0 0 ${glowBlur}px rgba(74, 144, 217, ${glowOpacity}), inset 0 0 ${glowBlur / 2}px rgba(74, 144, 217, ${glowOpacity * 0.5})`,
        pointerEvents: 'none',
        zIndex: 10,
      }}
    />
  );
};

export default ContextWindow;
