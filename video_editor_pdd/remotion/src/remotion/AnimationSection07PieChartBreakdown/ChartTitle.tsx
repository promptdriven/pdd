import React from 'react';
import { interpolate, useCurrentFrame, Easing } from 'remotion';
import { TITLE } from './constants';

export const ChartTitle: React.FC = () => {
  const frame = useCurrentFrame();

  // Fade in with scale animation
  const opacity = interpolate(frame, [0, 20], [0, 1], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.ease),
  });

  const scale = interpolate(frame, [0, 20], [0.9, 1.0], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.ease),
  });

  return (
    <div
      style={{
        position: 'absolute',
        left: TITLE.POSITION_X,
        top: TITLE.POSITION_Y,
        transform: `translateX(-50%) scale(${scale})`,
        opacity,
      }}
    >
      <h1
        style={{
          fontFamily: 'Inter, sans-serif',
          fontSize: TITLE.FONT_SIZE,
          fontWeight: 600,
          color: TITLE.COLOR,
          margin: 0,
          whiteSpace: 'nowrap',
        }}
      >
        {TITLE.TEXT}
      </h1>
    </div>
  );
};
