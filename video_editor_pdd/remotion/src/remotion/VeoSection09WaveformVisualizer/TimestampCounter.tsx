import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { TYPOGRAPHY, POSITIONS, ANIMATION, COLORS } from './constants';

/**
 * Ticking timestamp counter in the top-right corner.
 * Shows "0:24" incrementing to "0:27" over the duration.
 */
export const TimestampCounter: React.FC = () => {
  const frame = useCurrentFrame();

  // Map frame to seconds: 0->24, 90->27
  const seconds = interpolate(
    frame,
    [0, ANIMATION.totalDuration],
    [24, 27],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
    }
  );

  const displaySeconds = Math.floor(seconds);
  const timestamp = `0:${displaySeconds.toString().padStart(2, '0')}`;

  // Fade in/out
  const opacity = interpolate(
    frame,
    [
      ANIMATION.growStart,
      ANIMATION.labelFadeInEnd,
      ANIMATION.labelFadeOutStart,
      ANIMATION.shrinkEnd,
    ],
    [0, 0.7, 0.7, 0],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.inOut(Easing.quad),
    }
  );

  return (
    <div
      style={{
        position: 'absolute',
        left: POSITIONS.timestampX,
        top: POSITIONS.timestampY,
        fontFamily: TYPOGRAPHY.timestamp.fontFamily,
        fontWeight: TYPOGRAPHY.timestamp.fontWeight,
        fontSize: TYPOGRAPHY.timestamp.fontSize,
        color: COLORS.timestampText,
        opacity,
      }}
    >
      {timestamp}
    </div>
  );
};
