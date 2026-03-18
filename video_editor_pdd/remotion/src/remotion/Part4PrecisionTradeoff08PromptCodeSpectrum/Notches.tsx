import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { NOTCH_POSITIONS, NOTCH_SIZE, BAR_Y, BAR_HEIGHT, GRAY, TIMING } from './constants';

/**
 * Small triangular notch indicators along the right portion of the spectrum bar,
 * representing occasional dips into code territory.
 * Appear one by one starting at frame 120.
 */
export const Notches: React.FC = () => {
  const frame = useCurrentFrame();

  return (
    <>
      {NOTCH_POSITIONS.map((x, i) => {
        const startFrame = TIMING.notchStart + i * TIMING.notchStagger;
        const opacity = interpolate(
          frame,
          [startFrame, startFrame + TIMING.notchFadeDuration],
          [0, 1],
          {
            extrapolateLeft: 'clamp',
            extrapolateRight: 'clamp',
            easing: Easing.out(Easing.quad),
          }
        );

        if (opacity <= 0) return null;

        // Triangle notch pointing down, positioned just below the bar
        const notchY = BAR_Y + BAR_HEIGHT;

        return (
          <div
            key={x}
            style={{
              position: 'absolute',
              left: x - NOTCH_SIZE / 2,
              top: notchY,
              width: 0,
              height: 0,
              borderLeft: `${NOTCH_SIZE / 2}px solid transparent`,
              borderRight: `${NOTCH_SIZE / 2}px solid transparent`,
              borderTop: `${NOTCH_SIZE}px solid ${GRAY}`,
              opacity: 0.3 * opacity,
            }}
          />
        );
      })}
    </>
  );
};
