import React from 'react';
import { useCurrentFrame, interpolate } from 'remotion';
import { RED, FONT_SANS } from './constants';

/**
 * Displays an incrementing "Patches: N" counter at the bottom of the left panel.
 * Increments each time a new row appears.
 */
export const EffortCounter: React.FC<{ rowAppearFrames: number[] }> = ({ rowAppearFrames }) => {
  const frame = useCurrentFrame();

  // Count how many rows have appeared
  let count = 0;
  for (const f of rowAppearFrames) {
    if (frame >= f + 10) count++;
  }

  const opacity = interpolate(frame, [30, 45], [0, 1], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
  });

  if (count === 0) return null;

  return (
    <div
      style={{
        position: 'absolute',
        bottom: 300,
        left: 0,
        width: '100%',
        textAlign: 'center',
        fontFamily: FONT_SANS,
        fontSize: 16,
        color: RED,
        opacity,
      }}
    >
      Patches: {count}
    </div>
  );
};
