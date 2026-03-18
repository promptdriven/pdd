import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import {
  CONTEXT_WINDOW_SIZE,
  GRID_CENTER_X,
  GRID_CENTER_Y,
  HOLD_START,
  GRID_START,
} from './constants';

export const ContextWindow: React.FC = () => {
  const frame = useCurrentFrame();

  // Fade in
  const opacity = interpolate(frame, [0, 20], [0, 1], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
  });

  // Pulse glow during hold phase (after frame 600, relative to GRID_START)
  const holdRelative = frame - (HOLD_START - GRID_START);
  const pulseOpacity =
    holdRelative > 0
      ? interpolate(
          holdRelative % 90,
          [0, 45, 90],
          [0.12, 0.22, 0.12],
          { easing: Easing.inOut(Easing.sin) }
        )
      : 0.12;

  const left = GRID_CENTER_X - CONTEXT_WINDOW_SIZE / 2;
  const top = GRID_CENTER_Y - CONTEXT_WINDOW_SIZE / 2;

  return (
    <div
      style={{
        position: 'absolute',
        left,
        top,
        width: CONTEXT_WINDOW_SIZE,
        height: CONTEXT_WINDOW_SIZE,
        opacity,
        border: `2px solid rgba(74, 144, 217, 0.6)`,
        borderRadius: 4,
        backgroundColor: `rgba(74, 144, 217, 0.04)`,
        boxShadow: `0 0 8px rgba(74, 144, 217, ${pulseOpacity}), inset 0 0 8px rgba(74, 144, 217, 0.03)`,
        pointerEvents: 'none' as const,
        zIndex: 10,
      }}
    />
  );
};

export default ContextWindow;
