import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { COLORS, DIMENSIONS, ANIMATION_TIMING } from './constants';

export const RadialGlow: React.FC = () => {
  const frame = useCurrentFrame();

  // Phase 1: expand from 0 to full radius (frames 0-15)
  const radius = interpolate(
    frame,
    [ANIMATION_TIMING.backgroundFadeStart, ANIMATION_TIMING.backgroundFadeEnd],
    [0, DIMENSIONS.glowRadius],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    }
  );

  // Phase 2: pulse opacity from 0.3 -> 0.5 -> 0.3 (frames 45-60)
  let opacity = DIMENSIONS.glowBaseOpacity;
  if (frame >= ANIMATION_TIMING.glowPulseStart && frame <= ANIMATION_TIMING.glowPulseEnd) {
    const mid = (ANIMATION_TIMING.glowPulseStart + ANIMATION_TIMING.glowPulseEnd) / 2;
    if (frame <= mid) {
      opacity = interpolate(
        frame,
        [ANIMATION_TIMING.glowPulseStart, mid],
        [DIMENSIONS.glowBaseOpacity, DIMENSIONS.glowPulseOpacity],
        {
          extrapolateLeft: 'clamp',
          extrapolateRight: 'clamp',
          easing: Easing.inOut(Easing.sin),
        }
      );
    } else {
      opacity = interpolate(
        frame,
        [mid, ANIMATION_TIMING.glowPulseEnd],
        [DIMENSIONS.glowPulseOpacity, DIMENSIONS.glowBaseOpacity],
        {
          extrapolateLeft: 'clamp',
          extrapolateRight: 'clamp',
          easing: Easing.inOut(Easing.sin),
        }
      );
    }
  }

  // Fade in the glow alongside the background
  const fadeIn = interpolate(
    frame,
    [ANIMATION_TIMING.backgroundFadeStart, ANIMATION_TIMING.backgroundFadeEnd],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
    }
  );

  const diameter = radius * 2;

  return (
    <div
      style={{
        position: 'absolute',
        left: '50%',
        top: '50%',
        transform: 'translate(-50%, -50%)',
        width: diameter,
        height: diameter,
        borderRadius: '50%',
        background: `radial-gradient(circle, ${COLORS.glowCenter} 0%, transparent 70%)`,
        opacity: opacity * fadeIn,
      }}
    />
  );
};
