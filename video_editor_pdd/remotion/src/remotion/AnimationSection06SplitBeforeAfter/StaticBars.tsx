import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { COLORS, DIMENSIONS, POSITIONS, ANIMATION_TIMING } from './constants';

export const StaticBars: React.FC = () => {
  const frame = useCurrentFrame();

  return (
    <>
      {DIMENSIONS.barWidths.map((width, i) => {
        const barStart = ANIMATION_TIMING.barsStart + i * ANIMATION_TIMING.barStagger;
        const barEnd = barStart + 8;

        const opacity = interpolate(frame, [barStart, barEnd], [0, 1], {
          extrapolateLeft: 'clamp',
          extrapolateRight: 'clamp',
          easing: Easing.out(Easing.quad),
        });

        const scaleX = interpolate(frame, [barStart, barEnd], [0, 1], {
          extrapolateLeft: 'clamp',
          extrapolateRight: 'clamp',
          easing: Easing.out(Easing.cubic),
        });

        return (
          <div
            key={i}
            style={{
              position: 'absolute',
              left: 120,
              top: POSITIONS.barStartY + i * POSITIONS.barSpacing,
              width,
              height: DIMENSIONS.barHeight,
              backgroundColor: COLORS.staticBar,
              borderRadius: 4,
              opacity,
              transform: `scaleX(${scaleX})`,
              transformOrigin: 'left center',
            }}
          />
        );
      })}
    </>
  );
};
