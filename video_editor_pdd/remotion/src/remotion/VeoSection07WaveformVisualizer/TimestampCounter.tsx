import React from 'react';
import { useCurrentFrame, interpolate } from 'remotion';
import { POSITIONS, TYPOGRAPHY, COLORS, ANIMATION } from './constants';

export const TimestampCounter: React.FC = () => {
  const frame = useCurrentFrame();

  const opacity = interpolate(
    frame,
    [
      ANIMATION.backdropFadeStart, ANIMATION.backdropFadeEnd,
      ANIMATION.fadeOutStart, ANIMATION.fadeOutEnd,
    ],
    [0, 1, 1, 0],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' },
  );

  // Elapsed time: maps oscillation range to 0:08 → 0:11 (3 seconds)
  const elapsedProgress = interpolate(
    frame,
    [ANIMATION.oscillationStart, ANIMATION.oscillationEnd],
    [0, 1],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' },
  );

  const startSeconds = 8;
  const endSeconds = 11;
  const currentSeconds = startSeconds + (endSeconds - startSeconds) * elapsedProgress;
  const displaySeconds = Math.floor(currentSeconds);
  const timestamp = `0:${String(displaySeconds).padStart(2, '0')} / 0:11`;

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
        whiteSpace: 'nowrap',
      }}
    >
      {timestamp}
    </div>
  );
};
