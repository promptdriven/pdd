import React from 'react';
import { useCurrentFrame, interpolate } from 'remotion';
import { TRACK, COLORS, DIMENSIONS, ANIMATION_TIMING } from './constants';

interface PlayheadProps {
  currentX: number;
}

export const Playhead: React.FC<PlayheadProps> = ({ currentX }) => {
  const frame = useCurrentFrame();

  // Only visible during playhead sweep (frame 40-150)
  if (frame < ANIMATION_TIMING.playheadStart) {
    return null;
  }

  // Fade out after sweep ends (frame 120-150)
  const opacity = interpolate(
    frame,
    [ANIMATION_TIMING.fadeoutStart, ANIMATION_TIMING.fadeoutEnd],
    [1, 0],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
    }
  );

  return (
    <div
      style={{
        position: 'absolute',
        left: currentX,
        top: TRACK.y,
        transform: 'translate(-50%, -50%)',
        width: DIMENSIONS.playheadRadius * 2,
        height: DIMENSIONS.playheadRadius * 2,
        borderRadius: '50%',
        backgroundColor: COLORS.playhead,
        boxShadow: `0 0 ${DIMENSIONS.playheadGlowSize}px ${COLORS.playhead}, 0 0 ${DIMENSIONS.playheadGlowSize * 2}px rgba(255, 255, 255, 0.3)`,
        opacity,
      }}
    />
  );
};
