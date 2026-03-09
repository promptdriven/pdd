import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { COLORS, CANVAS, ANIMATION, DIMENSIONS } from './constants';

export const RadialGlowPulse: React.FC = () => {
  const frame = useCurrentFrame();

  // Pulse: 0% -> 80% -> 40%
  const glowOpacity = (() => {
    if (frame < ANIMATION.glowPulseStart) return 0;

    const midPoint =
      ANIMATION.glowPulseStart +
      (ANIMATION.glowPulseEnd - ANIMATION.glowPulseStart) * 0.5;

    if (frame <= midPoint) {
      // Rise from 0% to 80%
      return interpolate(
        frame,
        [ANIMATION.glowPulseStart, midPoint],
        [0, 0.8],
        {
          extrapolateLeft: 'clamp',
          extrapolateRight: 'clamp',
          easing: Easing.inOut(Easing.sin),
        },
      );
    }

    if (frame <= ANIMATION.glowPulseEnd) {
      // Fall from 80% to 40%
      return interpolate(
        frame,
        [midPoint, ANIMATION.glowPulseEnd],
        [0.8, 0.4],
        {
          extrapolateLeft: 'clamp',
          extrapolateRight: 'clamp',
          easing: Easing.inOut(Easing.sin),
        },
      );
    }

    // Hold at 40%
    return 0.4;
  })();

  return (
    <div
      style={{
        position: 'absolute',
        top: CANVAS.height / 2 - DIMENSIONS.glowDiameter / 2,
        left: CANVAS.width / 2 - DIMENSIONS.glowDiameter / 2,
        width: DIMENSIONS.glowDiameter,
        height: DIMENSIONS.glowDiameter,
        borderRadius: '50%',
        background: `radial-gradient(circle, ${COLORS.glowColor} 0%, transparent 70%)`,
        opacity: glowOpacity,
        pointerEvents: 'none',
      }}
    />
  );
};
