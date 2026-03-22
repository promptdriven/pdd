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
 * Uses a sine-eased opacity pulse cycling every GLOW_CYCLE_FRAMES.
 * Gradient blends from left panel colour (#4A90D9, top) to right panel colour (#D9944A, bottom).
 */
export const DividerGlow: React.FC<{
  /** Frames elapsed since this Sequence started */
  localFrame?: number;
}> = () => {
  const frame = useCurrentFrame();

  // Sine-eased pulse: oscillates 0 → 1 → 0 over GLOW_CYCLE_FRAMES
  const sinePhase = Math.sin((frame / GLOW_CYCLE_FRAMES) * Math.PI * 2);
  // Map -1…1 → 0.5…1.0 for opacity modulation (never fully invisible)
  const pulseFactor = 0.5 + 0.5 * ((sinePhase + 1) / 2);

  // Fade glow in over first 10 frames of the sequence
  const fadeIn = interpolate(frame, [0, 10], [0, 1], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.cubic),
  });

  const glowWidth = 8;
  const blurWidth = 30;

  return (
    <>
      {/* Core gradient glow — narrow, bright */}
      <div
        style={{
          position: 'absolute',
          top: 0,
          left: DIVIDER_X - glowWidth / 2,
          width: glowWidth,
          height: COMP_HEIGHT,
          background: `linear-gradient(to bottom, ${GLOW_COLOR_LEFT}, ${GLOW_COLOR_RIGHT})`,
          opacity: GLOW_MAX_OPACITY * fadeIn * pulseFactor,
          pointerEvents: 'none',
          zIndex: 7,
        }}
      />
      {/* Soft blurred halo around the glow */}
      <div
        style={{
          position: 'absolute',
          top: 0,
          left: DIVIDER_X - blurWidth / 2,
          width: blurWidth,
          height: COMP_HEIGHT,
          background: `linear-gradient(to bottom, ${GLOW_COLOR_LEFT}, ${GLOW_COLOR_RIGHT})`,
          opacity: GLOW_MAX_OPACITY * 0.6 * fadeIn * pulseFactor,
          filter: 'blur(10px)',
          pointerEvents: 'none',
          zIndex: 6,
        }}
      />
    </>
  );
};

export default DividerGlow;
