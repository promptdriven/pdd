import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import {
  COMP_HEIGHT,
  DIVIDER_X,
  GLOW_COLOR_LEFT,
  GLOW_COLOR_RIGHT,
  GLOW_MAX_OPACITY,
  GLOW_CYCLE_FRAMES,
} from './constants';

/**
 * A pulsing gradient glow on the vertical divider line.
 * Uses a sine oscillation to smoothly cycle between the two panel colours.
 */
export const DividerGlow: React.FC<{
  /** Frames elapsed since this Sequence started */
  localFrame?: number;
}> = () => {
  const frame = useCurrentFrame();

  // Sine oscillation: 0 → 1 → 0 over GLOW_CYCLE_FRAMES
  const cycle = Math.sin((frame / GLOW_CYCLE_FRAMES) * Math.PI * 2);
  // Map -1…1 → 0…1 for gradient mixing
  const mix = (cycle + 1) / 2;

  // Fade glow in over first 10 frames of the sequence
  const fadeIn = interpolate(frame, [0, 10], [0, 1], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.cubic),
  });

  const glowWidth = 20;

  return (
    <div
      style={{
        position: 'absolute',
        top: 0,
        left: DIVIDER_X - glowWidth / 2,
        width: glowWidth,
        height: COMP_HEIGHT,
        background: `linear-gradient(to bottom, ${GLOW_COLOR_LEFT}, ${GLOW_COLOR_RIGHT})`,
        opacity: GLOW_MAX_OPACITY * fadeIn,
        filter: `blur(8px)`,
        pointerEvents: 'none',
        // Shift the gradient position with the sine cycle to create the pulse
        transform: `scaleX(${0.6 + 0.4 * mix})`,
      }}
    />
  );
};

export default DividerGlow;
