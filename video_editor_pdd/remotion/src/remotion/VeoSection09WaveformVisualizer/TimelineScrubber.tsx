import React from 'react';
import { useCurrentFrame, interpolate } from 'remotion';
import { WAVEFORM, POSITIONS, ANIMATION, COLORS } from './constants';

/**
 * Vertical scrubber line that moves left-to-right across the waveform area
 * during the oscillation phase. Fades out during the shrink phase.
 */
export const TimelineScrubber: React.FC = () => {
  const frame = useCurrentFrame();

  // Scrubber moves linearly across waveform area during phase 2
  const scrubberX = interpolate(
    frame,
    [ANIMATION.oscillateStart, ANIMATION.oscillateEnd],
    [POSITIONS.waveformStartX, POSITIONS.waveformStartX + WAVEFORM.totalWidth],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
    }
  );

  // Fade in during grow phase, fade out during shrink phase
  const opacity = interpolate(
    frame,
    [
      ANIMATION.growStart,
      ANIMATION.growEnd,
      ANIMATION.shrinkStart,
      ANIMATION.shrinkEnd,
    ],
    [0, 0.6, 0.6, 0],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
    }
  );

  return (
    <div
      style={{
        position: 'absolute',
        left: scrubberX,
        top: WAVEFORM.baselineY - WAVEFORM.maxHeight - 20,
        width: 2,
        height: WAVEFORM.maxHeight + 40,
        backgroundColor: COLORS.scrubber,
        opacity,
        pointerEvents: 'none',
      }}
    />
  );
};
